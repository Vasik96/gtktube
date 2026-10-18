#!/usr/bin/env python3
"""GtkTube - a native GTK 4 YouTube client.

    sudo apt install python3-gi gir1.2-gtk-4.0 libgtk-4-media-gstreamer ffmpeg \
        gstreamer1.0-plugins-good gstreamer1.0-plugins-bad gstreamer1.0-libav \
        gir1.2-webkit-6.0 gir1.2-soup-3.0
    python3 gtktube.py            (GTKTUBE_DEBUG=1 python3 gtktube.py  prints timings)

Videos play in the native GTK player from a fixed-quality stream. yt-dlp and
deno are downloaded by the app itself (banner at the top) into
~/.local/share/gtktube/bin.

Playback: yt-dlp resolves the stream URLs, a tiny local HTTP server
fetches them from YouTube in 1-10 MB ranged chunks (the same trick yt-dlp uses
to avoid YouTube's per-connection throttling), and ffmpeg muxes the separate
video and audio streams (no re-encoding) into one stream for GTK's player.

1440p / 4K / HDR: YouTube only serves those as VP9 or AV1 (H.264 stops at
1080p). They are offered whenever GStreamer can decode the codec, whatever
your monitor is (an SDR monitor just shows HDR video without tone mapping).
If one stream fails, the app now only drops *that* codec at *that* height and
tries the next option at the same resolution before stepping down.
Environment variables:
    GTKTUBE_DEBUG=1     print which formats / decoders were found and why
                        a stream failed
    GTKTUBE_HWDEC=1     allow hardware decoders (much lighter for 4K)
    GTKTUBE_CLIENTS=... yt-dlp YouTube player clients (default
                        "default,android_vr", which exposes plain https
                        1440p / 4K streams)
"""
import ctypes
import ctypes.util
import hashlib
import http.client
import json
import math
import os
import platform
import queue
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from concurrent.futures import ThreadPoolExecutor
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from secrets import token_urlsafe

# googlevideo URLs are bound to the IP address yt-dlp resolved them from. If
# yt-dlp used IPv4 and Python connected over IPv6 (or the reverse) YouTube
# answers 403, intermittently. Pin media connections to IPv4; yt-dlp gets
# --force-ipv4 (see ytdlp_cmd).
_orig_getaddrinfo = socket.getaddrinfo


def _ipv4_for_googlevideo(host, *args, **kwargs):
    res = _orig_getaddrinfo(host, *args, **kwargs)
    if isinstance(host, str) and host.endswith(".googlevideo.com"):
        return [r for r in res if r[0] == socket.AF_INET] or res
    return res


socket.getaddrinfo = _ipv4_for_googlevideo

# Avoid hardware video decoders (VA-API / NVDEC): their separate video-surface
# path can leave audio playing while GTK renders a black frame, or decode only
# the first frame, on some desktop/GPU combinations. This covers H.264, VP9 and
# AV1. The saved setting takes precedence over the environment default.
DEFAULT_HW_DECODING = False


def _initial_hardware_decoding():
    config_home = os.environ.get("XDG_CONFIG_HOME") or os.path.join(
        os.path.expanduser("~"), ".config")
    settings_path = os.path.join(config_home, "gtktube", "settings.json")
    try:
        with open(settings_path) as settings_file:
            settings = json.load(settings_file)
    except (OSError, ValueError, UnicodeError):
        settings = None
    if (isinstance(settings, dict)
            and isinstance(settings.get("hardware_video_decoding"), bool)):
        return settings["hardware_video_decoding"]
    env_preference = os.environ.get("GTKTUBE_HWDEC")
    return (env_preference == "1" if env_preference is not None
            else DEFAULT_HW_DECODING)


HWDEC = _initial_hardware_decoding()
if not HWDEC:
    os.environ.setdefault("GST_PLUGIN_FEATURE_RANK", ",".join(
        f"{n}:NONE" for n in (
            "vah264dec", "vaapih264dec", "nvh264dec",
            "vavp9dec", "vaapivp9dec", "nvvp9dec",
            "vaav1dec", "vaapiav1dec", "nvav1dec",
            "vaapidecodebin", "v4l2slvp9dec", "v4l2slav1dec")))

import gi

gi.require_version("Gtk", "4.0")
gi.require_version("Gdk", "4.0")
from gi.repository import Gdk, Gio, GLib, Gtk, Pango  # noqa: E402

try:
    gi.require_version("GdkX11", "4.0")
    from gi.repository import GdkX11  # noqa: E402
except (ImportError, ValueError):
    GdkX11 = None

UA = "Mozilla/5.0 (X11; Linux x86_64; rv:130.0) Gecko/20100101 Firefox/130.0"
DESKTOP_UA = ("Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36")
SAFARI_UA = ("Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/605.1.15 "
             "(KHTML, like Gecko) Version/17.4 Safari/605.1.15")
API = "https://www.youtube.com/youtubei/v1/"
CTX = {"client": {"clientName": "WEB", "clientVersion": "2.20250925.01.00",
                  "hl": "en", "gl": "US"}}
CONF_DIR = os.path.join(GLib.get_user_config_dir(), "gtktube")
SUBS_FILE = os.path.join(CONF_DIR, "subs.json")
SETTINGS_FILE = os.path.join(CONF_DIR, "settings.json")
AVATARS_FILE = os.path.join(CONF_DIR, "avatars.json")
COOKIES = os.path.join(CONF_DIR, "cookies.txt")
TOOLS = os.path.join(GLib.get_user_data_dir(), "gtktube", "bin")
YTDLP = os.path.join(TOOLS, "yt-dlp")
DENO = os.path.join(TOOLS, "deno")
RELATED_W = 420
SEARCH_HISTORY_LIMIT = 20
DEBUG = bool(os.environ.get("GTKTUBE_DEBUG"))
# yt-dlp player clients. The default web client can hide its 1440p / 4K
# streams behind SABR (no plain URL), so android_vr is added: it returns
# ordinary https VP9 / AV1 streams up to 4K. (It is skipped by yt-dlp when
# you are signed in, because it does not support cookies; the others remain.)
YT_CLIENTS = os.environ.get("GTKTUBE_CLIENTS", "default,android_vr")
DEFAULT_CODEC_PREFERENCE = "vp9"
CODEC_PREFERENCE_ORDERS = {
    "vp9": ("vp9", "av1", "h264"),
    "av1": ("av1", "vp9", "h264"),
    "h264": ("h264", "vp9", "av1"),
}
CODEC_PREFERENCE_OPTIONS = (
    ("vp9", "VP9 → AV1 → H.264 (recommended)"),
    ("av1", "AV1 → VP9 → H.264"),
    ("h264", "H.264 → VP9 → AV1"),
)
# Containers ffmpeg may mux each codec into, in the order they are tried. If
# GTK's player never starts a stream in one container, the next is tried before
# the codec itself is given up on (H.264 only works well in MPEG-TS).
CONTAINER_ORDER = {"h264": ["mpegts"], "vp9": ["matroska", "fmp4"],
                   "av1": ["matroska", "fmp4"]}


def dlog(*args):
    if DEBUG:
        print("[gtktube]", *args, file=sys.stderr, flush=True)


CSS = b"""
.tube-card { padding: 6px; border-radius: 10px; }
.tube-card:hover { background: alpha(currentColor, 0.08); }
.tube-search-entry image:first-child { margin-right: 8px; }
.tube-thumb { border-radius: 10px; background: alpha(currentColor, 0.1); }
.tube-thumbbox { border-radius: 10px; }
.tube-avatar { border-radius: 999px; }
.tube-chan-banner { border-radius: 12px; background: alpha(currentColor, 0.1); }
.tube-meta { opacity: 0.65; font-size: 0.9em; }
.tube-title { font-weight: 600; }
.tube-title-big { font-weight: 600; font-size: 1.1em; }
.tube-badge { background: rgba(0,0,0,0.8); color: white; border-radius: 4px;
              padding: 1px 5px; font-size: 0.85em; font-weight: 600; }
.tube-banner { background: alpha(#f5a623, 0.28); padding: 8px 14px; }
.tube-shelf { background: alpha(currentColor, 0.05); border-radius: 14px;
              padding: 10px; }
.tube-player { background: black; border-radius: 10px; }
.tube-player label { color: white; }
.tube-playback-controls { background: rgba(0,0,0,0.7); border-radius: 10px;
                          padding: 4px 8px; }
.tube-playback-controls button { color: white; }
.tube-quality popover listview image { margin-left: 8px; }
button.tube-sub { background-image: none; background-color: #cc0000;
                  color: white; font-weight: 600; border-radius: 999px;
                  padding: 6px 18px; }
button.tube-sub:hover { background-color: #e60000; }
button.tube-unsub { background-image: none; background-color: #6e6e6e;
                    color: white; font-weight: 600; border-radius: 999px;
                    padding: 6px 18px; }
button.tube-unsub:hover { background-color: #858585; }
.tube-osd { background: rgba(0,0,0,0.75); border-radius: 12px;
            padding: 10px 24px; }
.tube-osd label { color: white; font-weight: 700; font-size: 1.25em; }
.tube-shorts-bg { background: #000; }
.tube-shorts-bg label { color: white; }
.tube-shorts-bg .tube-player { border-radius: 20px; }
.tube-shorts-bg button.tube-sbtn { background-image: none; color: white;
                                   background-color: rgba(255,255,255,0.16);
                                   border-radius: 999px; padding: 6px 16px; }
.tube-shorts-bg button.tube-sbtn:hover { background-color: rgba(255,255,255,0.28); }
"""

EMBED_ORIGIN = "https://gtktube.example"

# Page loaded into the WebKit view: the official YouTube player, autoplaying
# with subtitles on by default, reporting readiness / errors back to Python.
EMBED_HTML = """<!doctype html><html><head><meta charset="utf-8"><style>
html,body{margin:0;height:100%;background:#000;overflow:hidden}
iframe{width:100%;height:100%;border:0}</style></head><body><div id="p"></div>
<script src="https://www.youtube.com/iframe_api"></script>
<script>
var player;
function gtkMsg(o){var f=document.querySelector("iframe");
  if(f&&f.contentWindow)f.contentWindow.postMessage(o,"*")}
function post(m){try{window.webkit.messageHandlers.ytevent.postMessage(m)}catch(e){}}
function onYouTubeIframeAPIReady(){
  player=new YT.Player("p",{width:"100%",height:"100%",videoId:"__ID__",
    playerVars:{autoplay:1,rel:0,iv_load_policy:3,cc_load_policy:0,
                hl:"en",playsinline:1,origin:"__ORIGIN__"__LOOP__},
    events:{onReady:function(e){e.target.playVideo();post("ready")},
            onAutoplayBlocked:function(){try{player.playVideo()}catch(e){}},
            onError:function(e){post("error:"+e.data)}}});
}
</script></body></html>"""

# Injected into every frame at document start: make YouTube's player believe
# this is a mouse-driven desktop and not a touch device (the touch layout is
# what produces the "mobile" controls that never auto-hide).
NOTOUCH_JS = r"""(function(){
 try{Object.defineProperty(navigator,"maxTouchPoints",{get:function(){return 0}});}catch(e){}
 try{Object.defineProperty(navigator,"msMaxTouchPoints",{get:function(){return 0}});}catch(e){}
 ["ontouchstart","ontouchend","ontouchmove","ontouchcancel"].forEach(function(k){
  var o=window;while(o){try{delete o[k];}catch(e){}o=Object.getPrototypeOf(o);}});
 ["TouchEvent","Touch","TouchList"].forEach(function(k){
  try{delete window[k];}catch(e){}});
 try{var mm=window.matchMedia;
  window.matchMedia=function(q){
   if(/(pointer|hover)\s*:\s*(coarse|none)/.test(String(q)))
    return mm.call(window,"not all");
   return mm.call(window,q);};}catch(e){}
})();"""

# Accept YouTube's cookie-consent page inside the embedded player.
CONSENT_JS = r"""(function(){
 if(!/^(consent\.youtube\.com|consent\.google\.com)$/.test(location.hostname))return;
 var done=false,observer;
 function accept(){
  if(done)return;
  var buttons=document.querySelectorAll(
   "#introAgreeButton,button,[role=button],input[type=submit]");
  for(var i=0;i<buttons.length;i++){
   var b=buttons[i],label=(b.innerText||b.value||b.getAttribute("aria-label")||
                           b.textContent||"").trim();
   if(b.id==="introAgreeButton"||/^(accept all|i agree|agree|accept)$/i.test(label)){
    done=true;b.click();if(observer)observer.disconnect();return;
   }
  }
 }
 observer=new MutationObserver(accept);
 observer.observe(document,{subtree:true,childList:true,attributes:true});
 accept();
})();"""

# Injected into the youtube.com/embed frame: makes sure playback starts and
# that the control bar / icons / progress bar hide after 3 s without mouse
# movement (while playing and while no menu is open).
EMBED_JS = r"""(function(){
 if(!/youtube(-nocookie)?\.com\/embed\//.test(location.href))return;
 function pl(){return document.getElementById("movie_player");}
 function post(m){try{window.webkit.messageHandlers.ytevent.postMessage(m)}catch(e){}}
 var t0=Date.now(),last=Date.now(),hidden=false,lx=-1,ly=-1;
 var wantCC=false,cfgReady=false,ccTried=0,ccOffTries=0,ccOffAt=0;
 var volReady=false,pending=null,lastVol=-1;
 var seekT=null,seekAt=0,seekTimer=0;
 var root=document.documentElement;
 var sty=document.createElement("style");
 sty.textContent=".gtk-nocursor,.gtk-nocursor *{cursor:none !important}"+
  ".gtk-cc-off .ytp-caption-window-container{display:none !important}"+
  "video.gtk-seek-refresh{transform:translateZ(0)!important;"+
  "backface-visibility:hidden!important}";
 root.appendChild(sty);
 root.classList.add("gtk-cc-off");  // subtitles hidden until the saved choice says otherwise
 function applyCC(){root.classList.toggle("gtk-cc-off",!wantCC);}
 function menuOpen(){
  var b=document.querySelector(".ytp-settings-button");
  if(b&&b.getAttribute("aria-expanded")==="true")return true;
  var m=document.querySelector(".ytp-popup.ytp-settings-menu");
  return !!(m&&m.offsetParent!==null);}
 // ---- hide / show the control bar, icons, progress bar AND the cursor together
 function setHidden(h){
  var p=pl();hidden=h;
  root.classList.toggle("gtk-nocursor",h);
  if(!p)return;
  if(h){try{p.hideControls();}catch(e){}p.classList.add("ytp-autohide");}
  else{p.classList.remove("ytp-autohide");try{p.showControls();}catch(e){}}}
 // only real mouse movement / click, a pause, or leaving fullscreen bring them back
 function reveal(){last=Date.now();if(hidden)setHidden(false);}
 // volume / seek changes must NOT bring them back: re-hide if YouTube showed them
 function keepHidden(){
  if(!hidden)return;
  [30,250,700].forEach(function(ms){setTimeout(function(){
   if(!hidden)return;
   root.classList.add("gtk-nocursor");
   var p=pl();if(p){try{p.hideControls();}catch(e){}p.classList.add("ytp-autohide");}},ms);});}
 document.addEventListener("mousedown",reveal,true);
 document.addEventListener("mousemove",function(e){
  if(e.clientX===lx&&e.clientY===ly)return;  // ignore synthetic moves
  lx=e.clientX;ly=e.clientY;reveal();},true);
 // ---- double click on the video toggles fullscreen (handled by the app)
 document.addEventListener("dblclick",function(e){
  var t=e.target;
  if(t&&t.closest&&t.closest(".ytp-chrome-bottom,.ytp-chrome-top,.ytp-popup,.ytp-settings-button"))return;
  e.preventDefault();e.stopImmediatePropagation();post("fs");},true);
 // ---- subtitles: the choice is saved by the app; default OFF
 function ccBtn(){return document.querySelector(".ytp-subtitles-button");}
 function ccOn(){var b=ccBtn();return !!(b&&b.getAttribute("aria-pressed")==="true");}
 function ccUser(e){  // a real user action that changed the subtitle state
  if(!e.isTrusted)return;
  var before=ccOn();
  setTimeout(function(){var now=ccOn();
   if(now!==before){wantCC=now;applyCC();post("cc:"+(now?1:0));}},250);}
 document.addEventListener("click",function(e){
  if(e.target.closest&&e.target.closest(".ytp-subtitles-button,.ytp-popup"))ccUser(e);},true);
 document.addEventListener("keydown",function(e){
  if(e.key==="c"||e.key==="C")ccUser(e);},true);
 function ccTick(){
  if(!cfgReady)return;
  if(wantCC){
   var b=ccBtn();
   if(b&&!ccOn()&&Date.now()-t0<15000&&ccTried<6){ccTried++;b.click();}
   return;}
  // limited attempts only: the CSS above already hides the captions
  if(ccOn()&&ccOffTries<3&&Date.now()-ccOffAt>2000){
   ccOffTries++;ccOffAt=Date.now();
   try{pl().setOption("captions","track",{});}catch(e){}
   setTimeout(function(){
    if(!wantCC&&ccOn()){var b2=ccBtn();if(b2)b2.click();}},400);}}
 // ---- volume: set by the app (arrow keys / remembered value)
 function applyVol(){
  var p=pl();if(!p||!p.setVolume||pending===null)return;
  try{if(pending>0&&p.isMuted())p.unMute();p.setVolume(pending);}catch(e){}
  if(Math.round(p.getVolume())===pending){lastVol=pending;pending=null;}}
 // ---- seeking: coalesced so holding the key doesn't flood the player
 function seekBy(d){
  var p=pl();if(!p||!p.seekTo)return;
  var D=p.getDuration()||0;
  var base=(seekT!==null&&Date.now()-seekAt<800)?seekT:p.getCurrentTime();
  seekT=Math.max(0,base+d);
  if(D>0)seekT=Math.min(seekT,Math.max(0,D-0.5));
  seekAt=Date.now();
  if(!seekTimer)seekTimer=setTimeout(function(){
   seekTimer=0;
   try{p.seekTo(seekT,true);}catch(e){}
   seekAt=Date.now();},350);}
 document.addEventListener("seeked",function(e){
  var v=e.target;
  if(!v||v.tagName!=="VIDEO"||!v.requestVideoFrameCallback)return;
  v.requestVideoFrameCallback(function(){
   v.classList.add("gtk-seek-refresh");
   requestAnimationFrame(function(){v.classList.remove("gtk-seek-refresh");});
  });
 },true);
 window.addEventListener("message",function(e){
  var d=e.data;if(!d||!d.gtk)return;
  if(d.gtk==="cfg"){wantCC=!!d.cc;cfgReady=true;applyCC();}
  else if(d.gtk==="vol"){
   volReady=true;
   if(typeof d.v==="number"){pending=d.v;applyVol();if(d.show)keepHidden();}}
  else if(d.gtk==="seek"){seekBy(d.d);keepHidden();}
  else if(d.gtk==="reveal"){reveal();}});
 setInterval(function(){
  var p=pl();if(!p||!p.getPlayerState)return;
  var s=p.getPlayerState();
  if(Date.now()-t0<12000&&(s===-1||s===5)){try{p.playVideo();}catch(e){}}
  applyVol();
  if(volReady&&pending===null&&p.getVolume&&!p.isMuted()){
   var v=Math.round(p.getVolume());
   if(v!==lastVol){lastVol=v;post("vol:"+v);}}
  ccTick();
  if(s===1&&Date.now()-last>3000&&!menuOpen()){if(!hidden)setHidden(true);}
  else if((s===2||s===0)&&hidden){reveal();}  // paused / ended: show them
 },400);
})();"""

# -------------------------------------------------------------- persistence


def jload(path, default):
    try:
        with open(path) as f:
            return json.load(f)
    except Exception:  # noqa: BLE001
        return default


def jsave(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        json.dump(data, f)


AVATARS = jload(AVATARS_FILE, {})  # channel id -> avatar url


class Subs:
    def __init__(self):
        self.d = jload(SUBS_FILE, {})

    def save(self):
        jsave(SUBS_FILE, self.d)

    def toggle(self, cid, name):
        if cid in self.d:
            del self.d[cid]
        else:
            self.d[cid] = name
        self.save()
        return cid in self.d


# -------------------------------------------------------------------- tools


def tool_env():
    e = dict(os.environ)
    e["PATH"] = TOOLS + ":" + os.path.expanduser("~/.deno/bin") + ":" + \
        e.get("PATH", "")
    return e


def have_deno():
    return os.path.exists(DENO) or bool(shutil.which("deno", path=tool_env()["PATH"]))


def tools_ready():
    return os.path.exists(YTDLP) and have_deno()


def download(url, dest):
    tmp = dest + ".part"
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=120) as r, open(tmp, "wb") as f:
        shutil.copyfileobj(r, f)
    os.replace(tmp, dest)


def tool_versions():
    out = []
    try:
        v = subprocess.run([sys.executable, YTDLP, "--version"], capture_output=True,
                           text=True, timeout=60, env=tool_env()).stdout.strip()
        out.append("yt-dlp " + (v or "?"))
    except Exception:  # noqa: BLE001
        out.append("yt-dlp missing")
    try:
        dn = DENO if os.path.exists(DENO) else shutil.which(
            "deno", path=tool_env()["PATH"])
        v = subprocess.run([dn, "--version"], capture_output=True, text=True,
                           timeout=30).stdout.split()[1]
        out.append("deno " + v)
    except Exception:  # noqa: BLE001
        out.append("deno missing")
    return " · ".join(out)


def install_tools(report):
    """Download the latest yt-dlp (zipapp) and, if needed, deno."""
    os.makedirs(TOOLS, exist_ok=True)
    report("Downloading yt-dlp…")
    download("https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp",
             YTDLP)
    os.chmod(YTDLP, 0o755)
    if not have_deno():
        arch = {"x86_64": "x86_64", "amd64": "x86_64", "aarch64": "aarch64",
                "arm64": "aarch64"}.get(platform.machine().lower())
        if not arch:
            raise RuntimeError(f"No deno build for CPU {platform.machine()}; "
                               "install deno or node manually.")
        report("Downloading deno…")
        z = os.path.join(TOOLS, "deno.zip")
        download("https://github.com/denoland/deno/releases/latest/download/"
                 f"deno-{arch}-unknown-linux-gnu.zip", z)
        with zipfile.ZipFile(z) as zf:
            zf.extract("deno", TOOLS)
        os.remove(z)
        os.chmod(DENO, 0o755)
    return tool_versions()


def ytdlp_cmd(*args):
    # skip=hls,dash: we only use the plain https formats, so don't spend
    # requests on the manifests; fewer retries so failures surface quickly.
    # player_client: see YT_CLIENTS (adds android_vr for plain 1440p / 4K URLs).
    # --force-ipv4: the stream URLs are bound to the IP they were resolved
    # from, and our proxy also connects over IPv4 (see _ipv4_for_googlevideo).
    cmd = [sys.executable, YTDLP, "--no-warnings", "--force-ipv4",
           "--remote-components",
           "ejs:github", "--extractor-args",
           "youtube:skip=hls,dash,translated_subs;"
           f"player_client={YT_CLIENTS}",
           "--extractor-retries", "1", "--socket-timeout", "15"]
    if os.path.exists(COOKIES):
        cmd += ["--cookies", COOKIES]
    return cmd + list(args)


_INFO_CACHE = {}  # video id -> (time, slim info); URLs stay valid for hours
_INFO_TTL = 90 * 60
_info_locks = {}
_info_guard = threading.Lock()
_prefetching = set()
_prefetch_sem = threading.Semaphore(1)


def _slim_info(info):
    keep = ("format_id", "url", "ext", "vcodec", "acodec", "height", "width",
            "fps", "tbr", "abr", "protocol", "http_headers", "filesize",
            "format_note", "__yt_dlp_client", "dynamic_range", "language",
            "language_preference", "quality")
    # Keep the source-language hint so audio selection can prefer the original
    # Czech/English track, or English dubbing for videos originally in another
    # language.
    return {"duration": info.get("duration"),
            "description": info.get("description"),
            "language": info.get("language"),
            "original_language": info.get("original_language"),
            "formats": [{k: f[k] for k in keep if f.get(k) is not None}
                        for f in info.get("formats", [])]}


def ytdlp_info(url, fresh=False, newer_than=None):
    """Resolve stream info with yt-dlp (cached).

    fresh=True bypasses the cache, unless `newer_than` is given and the cached
    entry was resolved after that time (someone else already refreshed it).
    """
    if not os.path.exists(YTDLP):
        raise RuntimeError("Playback tools are not installed yet.")
    vid = url.rsplit("=", 1)[-1]
    with _info_guard:
        lock = _info_locks.setdefault(vid, threading.Lock())
    with lock:  # a hover-prefetch and a click for the same video share one run
        hit = _INFO_CACHE.get(vid)
        usable = (not fresh) or (newer_than is not None and hit is not None
                                 and hit[0] > newer_than)
        if hit and usable and time.time() - hit[0] < _INFO_TTL:
            dlog("yt-dlp cache hit", vid)
            return hit[1]
        t0 = time.monotonic()
        p = subprocess.run(ytdlp_cmd("-J", "--no-playlist",
                                     "--ignore-no-formats-error", url),
                           capture_output=True, text=True, timeout=120,
                           env=tool_env())
        if p.returncode != 0 or not p.stdout.strip():
            lines = [l for l in p.stderr.strip().splitlines() if l.strip()]
            raise RuntimeError(lines[-1][:300] if lines else "yt-dlp failed")
        info = _slim_info(json.loads(p.stdout))
        dlog(f"yt-dlp resolved {vid} in {time.monotonic() - t0:.1f}s")
        _INFO_CACHE[vid] = (time.time(), info)
        while len(_INFO_CACHE) > 16:
            _INFO_CACHE.pop(min(_INFO_CACHE, key=lambda k: _INFO_CACHE[k][0]))
        return info


def prefetch_info(vid):
    """Resolve a video's streams in the background (called on card hover)."""
    if not tools_ready():
        return
    with _info_guard:
        hit = _INFO_CACHE.get(vid)
        if (hit and time.time() - hit[0] < _INFO_TTL) or vid in _prefetching:
            return
        if not _prefetch_sem.acquire(blocking=False):
            return
        _prefetching.add(vid)

    def work():
        try:
            ytdlp_info(f"https://www.youtube.com/watch?v={vid}")
        except Exception:  # noqa: BLE001
            pass
        finally:
            with _info_guard:
                _prefetching.discard(vid)
                _prefetch_sem.release()
    threading.Thread(target=work, daemon=True).start()


def _clen(url):
    m = re.search(r"[?&]clen=(\d+)", url or "")
    return int(m.group(1)) if m else None


def fixed_stream_formats(info, available_codecs=None, exclude_codecs=(),
                         exclude_streams=(),
                         codec_preference=DEFAULT_CODEC_PREFERENCE):
    """Map height -> {"video", "audio", "container", "codec"} of streams ffmpeg
    can mux.

    H.264, VP9, and AV1 streams are selected when GStreamer can decode them.
    `exclude_codecs` removes a codec entirely; `exclude_streams` is a set of
    (codec, height) pairs that already failed, so one broken 4K VP9 stream
    doesn't take 1080p VP9 (or 4K AV1) down with it.

    HDR / 10-bit streams are fully allowed whatever the monitor is (they are
    shown without tone mapping, like an SDR screen showing an HDR video
    unconverted), but at equal height an SDR stream still wins. Then the chosen
    codec preference order is used, followed by fps and bitrate.
    """
    formats = info.get("formats", [])
    if (not isinstance(codec_preference, str) or
            codec_preference not in CODEC_PREFERENCE_ORDERS):
        codec_preference = DEFAULT_CODEC_PREFERENCE
    order = CODEC_PREFERENCE_ORDERS[codec_preference]
    codec_rank = {codec: len(order) - index
                  for index, codec in enumerate(order)}

    def ok(f):
        proto = str(f.get("protocol", ""))
        return bool(f.get("url")) and proto.startswith("http") \
            and not proto.startswith("m3u8")

    def vcodec(f):
        return str(f.get("vcodec") or "none")

    def acodec(f):
        return str(f.get("acodec") or "none")

    def video_codec(fmt):
        codec = vcodec(fmt).casefold()
        if codec.startswith("avc1"):
            return "h264"
        if codec.startswith(("vp09", "vp9")):
            return "vp9"
        if codec.startswith("av01"):
            return "av1"
        return None

    def is_plain_sdr(fmt):
        """True for 8-bit SDR. Used for RANKING only (SDR wins a tie);
        HDR / 10-bit streams are never excluded."""
        if str(fmt.get("dynamic_range") or "SDR").upper() != "SDR":
            return False
        codec = vcodec(fmt).casefold()
        parts = codec.split(".")
        try:
            if codec.startswith("av01"):  # av01.0.12M.10.0.110...
                return int(parts[3]) <= 8
            if codec.startswith("vp09") and len(parts) > 3:  # vp09.02.51.10
                return int(parts[3]) <= 8
            if codec.startswith("vp9") and len(parts) > 1:  # vp9.2
                return int(parts[1]) < 2
        except (IndexError, ValueError):
            pass
        return True

    def audio_codec(fmt):
        codec = acodec(fmt).casefold()
        if codec.startswith("mp4a"):
            return "aac"
        if codec.startswith("opus"):
            return "opus"
        if codec.startswith("vorbis"):
            return "vorbis"
        if codec.startswith("mp3"):
            return "mp3"
        return None

    def lang_code(value):
        # yt-dlp may report BCP-47 tags (en-US), bare ISO codes, or
        # language names. Only English and Czech are special-cased here.
        value = str(value or "").strip().casefold().replace("_", "-")
        if value in ("cs", "ces", "cze", "czech") or value.startswith("cs-"):
            return "cs"
        if value in ("en", "eng", "english") or value.startswith("en-"):
            return "en"
        return value

    source_lang = lang_code(info.get("original_language") or info.get("language"))
    # Preserve the original language when it is Czech or English. For any
    # other source language, prefer an available English dub; if none exists,
    # fall back to the best available audio track.
    wanted_lang = source_lang if source_lang in ("cs", "en") else "en"

    def audio_lang(fmt):
        lang = lang_code(fmt.get("language"))
        if lang in ("cs", "en"):
            return lang
        note = str(fmt.get("format_note") or "").casefold()
        if re.search(r"\b(czech|čeština|cesky|česky)\b", note):
            return "cs"
        if re.search(r"\b(english|eng)\b", note):
            return "en"
        return lang

    def language_rank(fmt):
        lang = audio_lang(fmt)
        if lang == wanted_lang:
            return 3
        if lang in ("cs", "en"):
            return 2
        # Unknown/original tracks remain a fallback when a preferred dub
        # is not exposed by this YouTube client.
        if lang and lang == source_lang:
            return 1
        return 0

    def audio_rank(fmt):
        note = str(fmt.get("format_note") or "").casefold()
        fmt_id = str(fmt.get("format_id") or "").casefold()
        is_drc = "drc" in note or fmt_id.endswith("-drc")
        return (language_rank(fmt), not is_drc,
                fmt.get("language_preference") or 0,
                fmt.get("abr") or 0, fmt.get("tbr") or 0)

    audio_only = [
        f for f in formats
        if ok(f) and vcodec(f) == "none" and acodec(f) != "none"
        and audio_codec(f)
        and (available_codecs is None or audio_codec(f) in available_codecs)]
    audio_preference = ("aac", "opus", "vorbis", "mp3")
    audio_codec_rank = {codec: len(audio_preference) - index
                        for index, codec in enumerate(audio_preference)}
    # Language takes priority over codec: an English Opus dub should beat a
    # foreign-language AAC track when English is what the user requested.
    best_audio = max(
        audio_only,
        key=lambda f: (language_rank(f), audio_codec_rank.get(audio_codec(f), 0),
                       audio_rank(f)), default=None)
    result = {}

    def consider(f, audio, container, codec):
        h = f["height"]
        # Muxed formats carry their own audio language; separately muxed
        # video uses the selected audio-only format's language.
        lang_source = audio if audio is not None else f
        rank = (language_rank(lang_source), is_plain_sdr(f),
                codec_rank.get(codec, 0), f.get("fps") or 0,
                f.get("tbr") or 0)
        prev = result.get(h)
        if prev is None or rank > prev["rank"]:
            result[h] = {"video": f, "audio": audio, "container": container,
                         "codec": codec, "rank": rank}

    for f in formats:
        codec = video_codec(f)
        if (not ok(f) or not f.get("height") or codec is None
                or codec in exclude_codecs
                or (codec, f["height"]) in exclude_streams
                or f.get("ext") not in ("mp4", "webm")
                or (available_codecs is not None
                    and codec not in available_codecs)):
            continue
        container = "mpegts" if codec == "h264" else "matroska"
        if acodec(f) == "none":
            if best_audio:
                consider(f, best_audio, container, codec)
        elif (audio_codec(f) and
              (available_codecs is None
               or audio_codec(f) in available_codecs)):
            consider(f, None, container, codec)
    return {h: {k: v for k, v in s.items() if k != "rank"}
            for h, s in result.items()}


def nearest_fixed_height(heights, target):
    """Choose the closest available fixed resolution, preferring higher ties."""
    return min(heights, key=lambda height: (abs(height - target), -height))


def screen_fit_height(heights, screen_height):
    """Choose the first available resolution at least as tall as the screen."""
    heights = sorted(heights)
    return next((height for height in heights if height >= screen_height),
                heights[-1])


def _x11_handles(window):
    if GdkX11 is None:
        return None
    display = window.get_display()
    surface = window.get_surface()
    if (not isinstance(display, GdkX11.X11Display)
            or not isinstance(surface, GdkX11.X11Surface)):
        return None
    library = ctypes.util.find_library("X11")
    if not library:
        return None
    xlib = ctypes.CDLL(library)
    xlib.XTranslateCoordinates.argtypes = (
        ctypes.c_void_p, ctypes.c_ulong, ctypes.c_ulong,
        ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_int),
        ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_ulong))
    xlib.XTranslateCoordinates.restype = ctypes.c_int
    xlib.XMoveWindow.argtypes = (
        ctypes.c_void_p, ctypes.c_ulong, ctypes.c_int, ctypes.c_int)
    xlib.XMoveWindow.restype = ctypes.c_int
    xlib.XInternAtom.argtypes = (ctypes.c_void_p, ctypes.c_char_p, ctypes.c_int)
    xlib.XInternAtom.restype = ctypes.c_ulong
    xlib.XGetWindowProperty.argtypes = (
        ctypes.c_void_p, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_long,
        ctypes.c_long, ctypes.c_int, ctypes.c_ulong,
        ctypes.POINTER(ctypes.c_ulong), ctypes.POINTER(ctypes.c_int),
        ctypes.POINTER(ctypes.c_ulong), ctypes.POINTER(ctypes.c_ulong),
        ctypes.POINTER(ctypes.POINTER(ctypes.c_ulong)))
    xlib.XGetWindowProperty.restype = ctypes.c_int
    xlib.XFree.argtypes = (ctypes.c_void_p,)
    xlib.XFree.restype = ctypes.c_int
    xlib.XFlush.argtypes = (ctypes.c_void_p,)
    xlib.XFlush.restype = ctypes.c_int
    return (xlib, ctypes.c_void_p(hash(display.get_xdisplay())),
            surface.get_xid(), display.get_xrootwindow())


def _x11_window_position(window):
    handles = _x11_handles(window)
    if handles is None:
        return None
    xlib, display, xid, root = handles
    x, y, child = ctypes.c_int(), ctypes.c_int(), ctypes.c_ulong()
    if not xlib.XTranslateCoordinates(
            display, xid, root, 0, 0,
            ctypes.byref(x), ctypes.byref(y), ctypes.byref(child)):
        return None
    atom = xlib.XInternAtom(display, b"_NET_FRAME_EXTENTS", 1)
    left, top = 0, 0
    if atom:
        actual_type, actual_format = ctypes.c_ulong(), ctypes.c_int()
        item_count, bytes_after = ctypes.c_ulong(), ctypes.c_ulong()
        data = ctypes.POINTER(ctypes.c_ulong)()
        status = xlib.XGetWindowProperty(
            display, xid, atom, 0, 4, 0, 0, ctypes.byref(actual_type),
            ctypes.byref(actual_format), ctypes.byref(item_count),
            ctypes.byref(bytes_after), ctypes.byref(data))
        if status == 0 and actual_format.value == 32 and item_count.value == 4:
            extents = [data[index] for index in range(4)]
            left, top = extents[0], extents[2]
        if data:
            xlib.XFree(data)
    return x.value - left, y.value - top


def _x11_move_window(window, x, y):
    handles = _x11_handles(window)
    if handles is None:
        return False
    xlib, display, xid = handles[:3]
    xlib.XMoveWindow(display, xid, x, y)
    xlib.XFlush(display)
    return True


YOUTUBE_HOST_RE = re.compile(
    r"^(?:(?:www|m|music)\.)?youtube\."
    r"(?:com|[a-z]{2}|(?:com|co)\.[a-z]{2})$")
VIDEO_ID_RE = re.compile(r"^[A-Za-z0-9_-]{11}$")


def youtube_video_id(value):
    """Return a video ID from a YouTube watch/share URL, or None."""
    value = value.strip()
    if not value:
        return None
    candidate = value if "://" in value else f"https://{value}"
    try:
        parsed = urllib.parse.urlsplit(candidate)
        host = (parsed.hostname or "").lower()
    except ValueError:
        return None
    if parsed.scheme not in ("http", "https"):
        return None
    short_host = host in ("youtu.be", "www.youtu.be")
    if not (short_host or YOUTUBE_HOST_RE.fullmatch(host)):
        return None
    path = [part for part in parsed.path.split("/") if part]
    video_id = ""
    if short_host and path:
        video_id = path[0]
    elif parsed.path.rstrip("/") == "/watch":
        video_id = urllib.parse.parse_qs(parsed.query).get("v", [""])[0]
    elif len(path) >= 2 and path[0] in ("shorts", "live", "embed", "v"):
        video_id = path[1]
    return video_id if VIDEO_ID_RE.fullmatch(video_id) else None


def is_youtube_url(value):
    candidate = value.strip()
    if not candidate:
        return False
    if "://" not in candidate:
        candidate = f"https://{candidate}"
    try:
        parsed = urllib.parse.urlsplit(candidate)
        host = (parsed.hostname or "").lower()
    except ValueError:
        return False
    if parsed.scheme not in ("http", "https"):
        return False
    return host in ("youtu.be", "www.youtu.be") or bool(
        YOUTUBE_HOST_RE.fullmatch(host))


def seek_position(start_time):
    """The exact -ss value used for `start_time` (rounded UP to the millisecond
    + 1 ms, so rounding can never push ffmpeg onto the previous keyframe)."""
    return math.ceil(start_time * 1000) / 1000 + 0.001


def ffmpeg_input_args(url, start_time=0, ss=None, itsoffset=0.0):
    """Input arguments. `ss` overrides the seek position (used as given);
    `itsoffset` shifts this input's timestamps (seconds, may be negative)."""
    args = ["-probesize", "500000", "-analyzeduration", "500000"]
    if ss is None and start_time > 0:
        ss = seek_position(start_time)
    if ss is not None and ss > 0:
        args.extend(["-ss", f"{ss:.3f}"])
    if itsoffset:
        args.extend(["-itsoffset", f"{itsoffset:.3f}"])
    return [*args, "-i", url]


def video_landing_offset(url, ss):
    """Where does ffmpeg's input seek REALLY put the video?

    With stream copy the video can only start on a keyframe at or before `ss`,
    while the audio starts exactly at `ss`; the difference (often 5-10 s) is
    heard as silence. Returns the first video packet's timestamp relative to
    `ss` (<= 0: e.g. -4.9 means the video starts 4.9 s before `ss`), or None.
    """
    cmd = [shutil.which("ffmpeg") or "ffmpeg", "-nostdin", "-hide_banner",
           "-loglevel", "error", *ffmpeg_input_args(url, ss=ss),
           "-map", "0:v:0", "-c", "copy", "-frames:v", "1",
           "-avoid_negative_ts", "disabled", "-f", "framecrc", "-"]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=25,
                             env=tool_env()).stdout
    except (OSError, subprocess.TimeoutExpired) as exc:
        dlog("video landing probe failed:", exc)
        return None
    tb = None
    for line in out.splitlines():
        m = re.match(r"#tb 0: (\d+)/(\d+)", line)
        if m:
            tb = int(m.group(1)) / int(m.group(2))
        elif line.strip() and not line.startswith("#") and tb:
            fields = [x.strip() for x in line.split(",")]
            try:
                return int(fields[2]) * tb
            except (IndexError, ValueError):
                return None
    return None


def nearest_video_keyframe(url, target, direction=0, origin=None):
    """Time of the video keyframe nearest `target` (so audio can start there too)."""
    cmd = [shutil.which("ffprobe") or "ffprobe", "-v", "error",
           "-skip_frame", "nokey", "-read_intervals", f"{target:.3f}%+7",
           "-i", url, "-select_streams", "v:0",
           "-show_entries", "frame=best_effort_timestamp_time", "-of", "csv=p=0"]
    result = subprocess.run(cmd, capture_output=True, text=True,
                            timeout=30, env=tool_env())
    if result.returncode:
        detail = result.stderr.strip().splitlines()
        raise RuntimeError(detail[-1][:300] if detail
                           else "FFprobe could not inspect the video.")
    keyframes = []
    for line in result.stdout.splitlines():
        try:
            keyframes.append(float(line.split(",", 1)[0]))
        except ValueError:
            continue
    if not keyframes:
        raise RuntimeError("No video keyframe was found near the seek position.")
    if origin is not None and direction:
        candidates = [timestamp for timestamp in keyframes
                      if (timestamp > origin if direction > 0
                          else timestamp < origin)]
        if candidates:
            keyframes = candidates
    return min(keyframes, key=lambda timestamp: (abs(timestamp - target),
                                                  -timestamp))


class Upstream:
    """Read one YouTube media URL in ranged chunks.

    YouTube throttles a single long request to a trickle after a short burst
    (the 'plays 2 seconds, then freezes' symptom). Requesting 1-10 MB ranges,
    like yt-dlp's own downloader does, keeps every request at full speed.
    A background thread reads ahead so chunk boundaries don't cause gaps.

    If YouTube answers 403 / 410 (expired or denied URL), `refresh` (when
    given) re-resolves this format's URL and the same range is retried, so the
    player never notices.
    """

    CHUNKS = (1 << 20, 3 << 20, 8 << 20, 10 << 20)

    def __init__(self, fmt, refresh=None):
        self.url = fmt["url"]
        self.fmt_id = fmt.get("format_id")
        self.refresh = refresh
        self.headers = dict(fmt.get("http_headers") or {})
        self.headers.setdefault("User-Agent", UA)
        self.headers["Accept-Encoding"] = "identity"
        self.size = int(fmt.get("filesize") or 0) or _clen(self.url)
        self._lock = threading.Lock()
        self._pool, self._plock = [], threading.Lock()
        self._rlock = threading.Lock()
        self._refreshes, self._url_stamp = 0, time.time()

    # --- connections are kept alive and reused: each ffmpeg seek or chunk
    # --- boundary then costs one round trip instead of a new TLS handshake
    def open_range(self, first, last):
        """Return (connection, response) for bytes first-last (follows redirects)."""
        for _hop in range(5):
            u = urllib.parse.urlsplit(self.url)
            target = (u.path or "/") + ("?" + u.query if u.query else "")
            conn = None
            with self._plock:
                while self._pool and conn is None:
                    c = self._pool.pop()
                    if c.host_key == u.netloc:
                        conn = c
                    else:
                        c.close()
            fresh = conn is None
            if fresh:
                cls = (http.client.HTTPSConnection if u.scheme == "https"
                       else http.client.HTTPConnection)
                conn = cls(u.netloc, timeout=15)
                conn.host_key = u.netloc
            try:
                conn.request("GET", target,
                             headers={**self.headers, "Range": f"bytes={first}-{last}"})
                resp = conn.getresponse()
            except (OSError, http.client.HTTPException):
                conn.close()
                if fresh:
                    raise
                continue  # a reused connection had gone stale: try another
            if resp.status in (301, 302, 303, 307, 308):
                loc = resp.getheader("Location")
                resp.read()
                conn.close()
                if not loc:
                    raise RuntimeError("redirect without a Location")
                self.url = urllib.parse.urljoin(self.url, loc)
                with self._plock:
                    for c in self._pool:
                        c.close()
                    self._pool = []
                continue
            if resp.status not in (200, 206):
                try:
                    resp.read(200)
                finally:
                    conn.close()
                dlog(f"HTTP {resp.status} fmt={self.fmt_id} host={u.netloc} "
                     f"range={first}-{last} pot={'pot=' in self.url} "
                     f"reused_conn={not fresh} refreshes={self._refreshes}")
                raise urllib.error.HTTPError(self.url, resp.status, resp.reason,
                                             resp.headers, None)
            return conn, resp
        raise RuntimeError("the media server redirected too many times")

    def _refresh_url(self, failed_stamp):
        """Re-resolve this format's URL after a 403/410. True if a usable URL
        is now set (either refreshed here or by another thread meanwhile)."""
        if not self.refresh:
            return False
        with self._rlock:
            if self._url_stamp > failed_stamp:  # someone already refreshed it
                return True
            if self._refreshes >= 4:
                return False
            self._refreshes += 1
            try:
                f = self.refresh(self._url_stamp)
            except Exception as exc:  # noqa: BLE001
                dlog("url refresh failed:", exc)
                return False
            if not f or not f.get("url"):
                return False
            self.url = f["url"]
            self.headers.update(f.get("http_headers") or {})
            self.headers["Accept-Encoding"] = "identity"
            with self._plock:
                for c in self._pool:
                    c.close()
                self._pool = []
            self._url_stamp = time.time()
            dlog("refreshed expired/denied URL for format", self.fmt_id)
            return True

    def _open(self, first, last):
        """open_range, transparently refreshing the URL on 403 / 410."""
        stamp = self._url_stamp
        try:
            return self.open_range(first, last)
        except urllib.error.HTTPError as exc:
            if exc.code in (403, 410) and self._refresh_url(stamp):
                return self.open_range(first, last)
            raise

    def _release(self, conn, resp):
        """Keep a fully-read keep-alive connection for the next request."""
        if resp.isclosed() and not resp.will_close:
            with self._plock:
                if len(self._pool) < 4:
                    self._pool.append(conn)
                    return
        conn.close()

    def total(self):
        with self._lock:
            if not self.size:
                conn, r = self._open(0, 0)
                try:
                    m = re.search(r"/(\d+)\s*$", r.getheader("Content-Range", ""))
                    r.read()
                except Exception:
                    conn.close()
                    raise
                self._release(conn, r)
                if not m:
                    raise RuntimeError("the media server did not report a size")
                self.size = int(m.group(1))
            return self.size

    @staticmethod
    def _put(q, item, stop):
        while not stop.is_set():
            try:
                q.put(item, timeout=0.5)
                return True
            except queue.Full:
                pass
        return False

    def _produce(self, first, last, q, stop):
        pos, step, fails = first, 0, 0
        try:
            while pos <= last and not stop.is_set():
                size = self.CHUNKS[min(step, len(self.CHUNKS) - 1)]
                end = min(pos + size - 1, last)
                before = pos
                conn, done = None, False
                try:
                    conn, r = self._open(pos, end)
                    while not stop.is_set():
                        blk = r.read(65536)
                        if not blk:
                            done = True
                            break
                        if not self._put(q, blk, stop):
                            return
                        pos += len(blk)
                except (OSError, http.client.HTTPException) as exc:
                    fails += 1
                    fatal = (isinstance(exc, urllib.error.HTTPError)
                             and exc.code in (400, 403, 404, 410))
                    if fails > 3 or fatal:
                        raise
                    time.sleep(0.4 * fails)
                    continue
                finally:
                    if conn is not None:
                        if done:
                            self._release(conn, r)
                        else:
                            conn.close()
                if pos == before:  # empty answer: don't spin forever
                    fails += 1
                    if fails > 3:
                        raise RuntimeError("the media server sent no data")
                else:
                    fails = 0
                    step += 1
        except Exception as exc:  # noqa: BLE001
            self._put(q, exc, stop)
        finally:
            self._put(q, None, stop)

    def stream(self, first, last):
        q = queue.Queue(maxsize=48)  # ~3 MB read-ahead
        stop = threading.Event()
        threading.Thread(target=self._produce, args=(first, last, q, stop),
                         daemon=True).start()
        try:
            while True:
                item = q.get()
                if item is None:
                    return
                if isinstance(item, BaseException):
                    raise item
                yield item
        finally:
            stop.set()


class FixedStreamServer(ThreadingHTTPServer):
    """Local HTTP server with two kinds of URL:

      /u/<token>/v|a   range-capable proxy for the video / audio file; it
                       fetches from YouTube in chunks (see Upstream)
      /s/<token>       the muxed stream: ffmpeg reads the two proxy URLs and
                       copies both streams into one MPEG-TS or Matroska
    """

    daemon_threads = True
    allow_reuse_address = True
    request_queue_size = 32

    def __init__(self, on_error):
        self.streams = {}
        self.processes = {}
        self.on_error = on_error
        self._lock = threading.Lock()

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def log_message(self, _format, *_args):
                pass

            def do_HEAD(self):
                self._route(True)

            def do_GET(self):
                self._route(False)

            def _route(self, head):
                parts = self.path.partition("?")[0].strip("/").split("/")
                spec = None
                if len(parts) >= 2:
                    with self.server._lock:
                        spec = self.server.streams.get(parts[1])
                if spec is None:
                    self.send_error(404)
                elif parts[0] == "u" and len(parts) == 3:
                    self._proxy(parts[1], spec, parts[2], head)
                elif parts[0] == "s":
                    self._mux(parts[1], spec, head)
                else:
                    self.send_error(404)

            # --- /u/: ranged proxy for one YouTube file -------------------
            def _proxy(self, token, spec, key, head):
                up = spec["up"].get(key)
                if up is None:
                    self.send_error(404)
                    return
                try:
                    total = up.total()
                except Exception as exc:  # noqa: BLE001
                    self.server.on_error(
                        token, f"Could not reach YouTube's media server: {exc}")
                    self.send_error(502)
                    return
                first, last, partial = 0, total - 1, False
                m = re.match(r"bytes=(\d*)-(\d*)$",
                             (self.headers.get("Range") or "").strip())
                if m and (m.group(1) or m.group(2)):
                    partial = True
                    if m.group(1):
                        first = int(m.group(1))
                        if m.group(2):
                            last = min(int(m.group(2)), total - 1)
                    else:  # suffix range: the last N bytes
                        first = max(0, total - int(m.group(2)))
                if first >= total:
                    self.send_response(416)
                    self.send_header("Content-Range", f"bytes */{total}")
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                    return
                self.send_response(206 if partial else 200)
                self.send_header("Content-Type",
                                 "audio/mp4" if key == "a" else "video/mp4")
                self.send_header("Accept-Ranges", "bytes")
                self.send_header("Content-Length", str(last - first + 1))
                if partial:
                    self.send_header("Content-Range",
                                     f"bytes {first}-{last}/{total}")
                self.send_header("Connection", "close")
                self.end_headers()
                self.close_connection = True
                if head:
                    return
                try:
                    for blk in up.stream(first, last):
                        self.wfile.write(blk)
                except (BrokenPipeError, ConnectionResetError, TimeoutError):
                    pass  # ffmpeg closed the connection (e.g. after a seek)
                except Exception as exc:  # noqa: BLE001
                    self.server.on_error(token, f"Download from YouTube "
                                                f"failed: {exc}")

            # --- /s/: muxed stream ----------------------------------------
            def _mux(self, token, spec, head):
                formats = spec["formats"]
                container = formats.get("container", "mpegts")
                ctype = {"mpegts": "video/mp2t", "matroska": "video/x-matroska",
                         "fmp4": "video/mp4"}.get(container, "video/mp2t")
                if head:
                    self.send_response(200)
                    self.send_header("Content-Type", ctype)
                    self.send_header("Cache-Control", "no-store")
                    self.send_header("Accept-Ranges", "none")
                    self.send_header("Connection", "close")
                    self.end_headers()
                    self.close_connection = True
                    return
                base = f"http://127.0.0.1:{self.server.server_port}/u/{token}"
                start_time = spec.get("start_time", 0)
                if start_time > 0:
                    try:
                        start_time = nearest_video_keyframe(
                            f"{base}/v", start_time,
                            spec.get("seek_direction", 0), spec.get("seek_origin"))
                    except (OSError, RuntimeError, subprocess.TimeoutExpired) as exc:
                        # no keyframe info: seek to the exact time instead
                        dlog("keyframe lookup failed:", exc)
                        start_time = spec.get("start_time", 0)
                has_audio_file = bool(formats.get("audio"))
                video_ss, audio_ss, audio_shift = None, None, 0.0
                if start_time > 0:
                    video_ss = seek_position(start_time)
                    landed = video_landing_offset(f"{base}/v", video_ss)
                    dlog(f"seek {video_ss:.3f}s: video lands at offset {landed}")
                    if landed is not None and landed < -0.05:
                        # The video starts `landed` seconds before the seek
                        # position. Start the audio at the same source time and
                        # shift its timestamps so both stay in sync: no silence.
                        audio_ss = max(0.0, video_ss + landed)
                        audio_shift = audio_ss - video_ss
                        start_time = max(0.0, video_ss + landed)
                    with self.server._lock:
                        current = self.server.streams.get(token)
                        if current is not None:
                            current["actual_start_time"] = start_time
                cmd = [shutil.which("ffmpeg") or "ffmpeg", "-nostdin",
                       "-hide_banner", "-loglevel", "error",
                       *ffmpeg_input_args(f"{base}/v", ss=video_ss)]
                if has_audio_file:
                    cmd += ffmpeg_input_args(
                        f"{base}/a",
                        ss=video_ss if audio_ss is None else audio_ss,
                        itsoffset=audio_shift)
                cmd += ["-map", "0:v:0", "-map",
                        "1:a:0" if has_audio_file else "0:a:0", "-c", "copy",
                        "-avoid_negative_ts", "make_zero", "-flush_packets", "1",
                        "-max_interleave_delta", "1000000"]
                if container == "mpegts":
                    cmd += ["-muxdelay", "0.2", "-muxpreload", "0.2", "-mpegts_flags",
                            "+resend_headers", "-f", "mpegts", "pipe:1"]
                elif container == "matroska":
                    cmd += ["-cluster_time_limit", "1000", "-cluster_size_limit",
                            "1048576", "-live", "1", "-f", "matroska", "pipe:1"]
                else:  # fragmented MP4: short fragments keep audio next to video
                    cmd += ["-movflags",
                            "+empty_moov+default_base_moof+separate_moof",
                            "-frag_duration", "200000", "-f", "mp4", "pipe:1"]
                dlog("ffmpeg:", " ".join(cmd))
                t0 = time.monotonic()
                try:
                    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                                            stderr=subprocess.PIPE, bufsize=0,
                                            env=tool_env())
                except OSError as exc:
                    self.server.on_error(token, str(exc))
                    self.send_error(502, f"Could not start FFmpeg: {exc}")
                    return
                with self.server._lock:
                    if token not in self.server.streams:
                        proc.terminate()
                    self.server.processes.setdefault(token, []).append(proc)
                errors = []
                # ~40 MB of read-ahead: ffmpeg runs well ahead of playback, so a
                # network hiccup doesn't freeze the picture.
                output = queue.Queue(maxsize=640)

                def read_errors():
                    for line in proc.stderr:
                        errors.append(line.decode("utf-8", "replace").strip())
                        del errors[:-20]

                def read_output():
                    try:
                        while chunk := os.read(proc.stdout.fileno(), 64 * 1024):
                            while True:
                                try:
                                    output.put(chunk, timeout=0.2)
                                    break
                                except queue.Full:
                                    if proc.poll() is not None:
                                        return
                    finally:
                        try:
                            output.put(None, timeout=0.2)
                        except queue.Full:
                            pass

                threading.Thread(target=read_errors, daemon=True).start()
                threading.Thread(target=read_output, daemon=True).start()
                disconnected = False
                try:
                    try:
                        # 4K streams are big: give ffmpeg more time to probe
                        chunk = output.get(timeout=40)
                    except queue.Empty:
                        detail = "Timed out waiting for FFmpeg to read the video."
                        self.server.on_error(token, detail)
                        self.send_error(504, detail)
                        return
                    if chunk is None:
                        detail = "\n".join(errors[-5:]) or \
                            f"FFmpeg exited with status {proc.poll()}."
                        self.server.on_error(token, detail)
                        self.send_error(502, detail)
                        return
                    dlog(f"ffmpeg first data after {time.monotonic() - t0:.1f}s")
                    self.send_response(200)
                    self.send_header("Content-Type", ctype)
                    self.send_header("Transfer-Encoding", "chunked")
                    self.send_header("Cache-Control", "no-store")
                    self.send_header("Accept-Ranges", "none")
                    self.end_headers()
                    self.close_connection = True
                    while chunk is not None:
                        self.wfile.write(f"{len(chunk):X}\r\n".encode("ascii"))
                        self.wfile.write(chunk)
                        self.wfile.write(b"\r\n")
                        self.wfile.flush()
                        try:
                            chunk = output.get(timeout=30)
                        except queue.Empty:
                            self.server.on_error(
                                token, "Timed out while receiving video data.")
                            disconnected = True
                            break
                    if not disconnected:
                        self.wfile.write(b"0\r\n\r\n")
                except (BrokenPipeError, ConnectionResetError, TimeoutError):
                    disconnected = True
                finally:
                    if proc.poll() is None:
                        proc.terminate()
                        try:
                            proc.wait(timeout=3)
                        except subprocess.TimeoutExpired:
                            proc.kill()
                            proc.wait()
                    with self.server._lock:
                        active = self.server.processes.get(token, [])
                        if proc in active:
                            active.remove(proc)
                        if not active:
                            self.server.processes.pop(token, None)
                if not disconnected and proc.returncode:
                    detail = "\n".join(errors[-5:]) or \
                        f"FFmpeg exited with status {proc.returncode}."
                    self.server.on_error(token, detail)

        super().__init__(("127.0.0.1", 0), Handler)

    def add(self, spec, start_time=0, seek_direction=0, seek_origin=None,
            video_id=None):
        def make_refresh(fmt):
            """Callback that re-resolves one format's URL (for 403 / 410)."""
            if not video_id:
                return None
            fid = fmt.get("format_id")

            def refresh(newer_than):
                info = ytdlp_info(
                    f"https://www.youtube.com/watch?v={video_id}",
                    fresh=True, newer_than=newer_than)
                return next((f for f in info["formats"]
                             if f.get("format_id") == fid), None)
            return refresh

        token = token_urlsafe(24)
        up = {"v": Upstream(spec["video"], make_refresh(spec["video"]))}
        if spec.get("audio"):
            up["a"] = Upstream(spec["audio"], make_refresh(spec["audio"]))
        with self._lock:
            self.streams[token] = {
                "formats": spec,
                "up": up,
                "start_time": max(0, float(start_time)),
                "seek_direction": seek_direction,
                "seek_origin": seek_origin,
            }
        return f"http://127.0.0.1:{self.server_port}/s/{token}"

    def get_start_time(self, url):
        token = url.rsplit("/", 1)[-1]
        with self._lock:
            spec = self.streams.get(token)
            if spec is None:
                return None
            return spec.get("actual_start_time", spec["start_time"])

    def remove(self, url):
        if not url:
            return
        token = url.rsplit("/", 1)[-1]
        with self._lock:
            self.streams.pop(token, None)
            processes = self.processes.pop(token, [])
        for proc in processes:
            if proc.poll() is None:
                proc.terminate()

    def close(self):
        with self._lock:
            tokens = list(self.streams)
        for token in tokens:
            self.remove(f"http://127.0.0.1/{token}")
        self.shutdown()
        self.server_close()


# ------------------------------------------------------------------- webkit

_WK = None


def webkit_env():
    """Return (WebKit module, shared NetworkSession) or (None, None).

    One persistent session is shared by the Google sign-in window and the
    embedded player, so being signed in also applies to playback.
    """
    global _WK
    if _WK is None:
        try:
            gi.require_version("WebKit", "6.0")
            from gi.repository import WebKit
            base = os.path.join(CONF_DIR, "webkit")
            os.makedirs(base, exist_ok=True)
            sess = WebKit.NetworkSession.new(base + "/data", base + "/cache")
            try:  # let the player (an iframe) see the Google login cookies
                sess.set_itp_enabled(False)
                sess.get_cookie_manager().set_accept_policy(
                    WebKit.CookieAcceptPolicy.ALWAYS)
            except Exception:  # noqa: BLE001
                pass
            _WK = (WebKit, sess)
        except Exception:  # noqa: BLE001
            _WK = (None, None)
    return _WK


# --------------------------------------------------------------------- auth


def parse_netscape(path):
    rows = []
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            http = False
            if line.startswith("#HttpOnly_"):
                line, http = line[len("#HttpOnly_"):], True
            elif line.startswith("#") or not line.strip():
                continue
            p = line.split("\t")
            if len(p) == 7:
                try:
                    exp = int(p[4])
                except ValueError:
                    exp = 0
                rows.append((p[0], p[2], p[3] == "TRUE", exp, p[5], p[6], http))
    return rows


def read_cookies():
    try:
        rows = [r for r in parse_netscape(COOKIES)
                if r[0].lstrip(".").endswith(("youtube.com", "google.com"))]
    except OSError:
        return {}
    rows.sort(key=lambda r: "youtube" not in r[0])  # youtube.com wins on clash
    jar = {}
    for r in rows:
        jar.setdefault(r[4], r[5])
    return jar


def logged_in():
    c = read_cookies()
    return bool(c.get("SAPISID") or c.get("__Secure-3PAPISID"))


def auth_headers():
    c = read_cookies()
    sid = c.get("SAPISID") or c.get("__Secure-3PAPISID")
    if not sid:
        return {}
    ts = int(time.time())
    h = hashlib.sha1(f"{ts} {sid} https://www.youtube.com".encode()).hexdigest()
    return {"Cookie": "; ".join(f"{k}={v}" for k, v in c.items()),
            "Authorization": f"SAPISIDHASH {ts}_{h}",
            "X-Goog-AuthUser": "0", "X-Origin": "https://www.youtube.com"}


def write_netscape(rows):
    """rows: (domain, path, secure, expires, name, value, httponly)"""
    os.makedirs(CONF_DIR, exist_ok=True)
    seen, lines = set(), ["# Netscape HTTP Cookie File"]
    for dom, path, secure, exp, name, val, http in rows:
        if not dom.lstrip(".").endswith(("youtube.com", "google.com")):
            continue  # never keep cookies of other sites
        if (dom, path, name) in seen:
            continue
        seen.add((dom, path, name))
        lines.append("\t".join([("#HttpOnly_" if http else "") + dom,
                                "TRUE" if dom.startswith(".") else "FALSE",
                                path, "TRUE" if secure else "FALSE",
                                str(exp or int(time.time()) + 86400 * 365),
                                name, val]))
    with open(COOKIES, "w") as f:
        f.write("\n".join(lines) + "\n")
    os.chmod(COOKIES, 0o600)


# ----------------------------------------------------------------- innertube


def innertube(endpoint, **body):
    body["context"] = CTX
    headers = {"Content-Type": "application/json", "User-Agent": UA,
               "Origin": "https://www.youtube.com",
               "X-YouTube-Client-Name": "1",
               "X-YouTube-Client-Version": CTX["client"]["clientVersion"]}
    headers.update(auth_headers())
    req = urllib.request.Request(API + endpoint + "?prettyPrint=false",
                                 json.dumps(body).encode(), headers)
    try:
        with urllib.request.urlopen(req, timeout=20) as r:
            return json.load(r)
    except urllib.error.HTTPError as e:
        raise RuntimeError(f"HTTP {e.code} from {endpoint}: "
                           f"{e.read()[:160].decode('utf8', 'replace')}") from None


def walk(o):
    if isinstance(o, dict):
        yield o
        for v in o.values():
            yield from walk(v)
    elif isinstance(o, list):
        for v in o:
            yield from walk(v)


def youtube_search_suggestions(query):
    """Fetch YouTube autocomplete suggestions, including signed-in history."""
    params = urllib.parse.urlencode({
        "client": "youtube", "ds": "yt", "gs_ri": "youtube",
        "hl": CTX["client"]["hl"], "gl": CTX["client"]["gl"], "q": query})
    url = "https://suggestqueries-clients6.youtube.com/complete/search?" + params
    headers = {"User-Agent": DESKTOP_UA, "Referer": "https://www.youtube.com/"}
    try:
        cookie_rows = parse_netscape(COOKIES)
    except OSError:
        cookie_rows = []
    youtube_cookies = {}
    for cookie_row in cookie_rows:
        domain, expires, name, value = (
            cookie_row[0], cookie_row[3], cookie_row[4], cookie_row[5])
        normalized_domain = domain.lower().lstrip(".")
        if (normalized_domain != "youtube.com"
                and not normalized_domain.endswith(".youtube.com")):
            continue
        if expires and expires < int(time.time()):
            continue
        youtube_cookies[name] = value
    if youtube_cookies:
        headers["Cookie"] = "; ".join(
            f"{name}={value}" for name, value in youtube_cookies.items())
        sid = (youtube_cookies.get("SAPISID")
               or youtube_cookies.get("__Secure-3PAPISID"))
        if sid:
            ts = int(time.time())
            digest = hashlib.sha1(
                f"{ts} {sid} https://www.youtube.com".encode()).hexdigest()
            headers["Authorization"] = f"SAPISIDHASH {ts}_{digest}"
            headers["X-Goog-AuthUser"] = "0"
            headers["X-Origin"] = "https://www.youtube.com"
    req = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=8) as response:
            payload = response.read().decode("utf-8")
    except urllib.error.HTTPError as exc:
        raise RuntimeError(
            f"YouTube suggestions failed with HTTP {exc.code}.") from None
    start, end = payload.find("("), payload.rfind(")")
    if start < 0 or end <= start:
        raise RuntimeError("YouTube returned an invalid suggestions response.")
    data = json.loads(payload[start + 1:end])
    if not isinstance(data, list) or len(data) < 2 \
            or not isinstance(data[1], list):
        raise RuntimeError("YouTube returned an invalid suggestions response.")
    suggestions, seen = [], set()
    for suggestion in data[1]:
        if not isinstance(suggestion, list) or not suggestion:
            continue
        text = str(suggestion[0]).strip()
        if not text or text.casefold() in seen:
            continue
        seen.add(text.casefold())
        marker = " ".join(str(part) for part in suggestion[1:])
        suggestions.append((text, "history" in marker.casefold()))
    return suggestions[:8]


def dig(o, *path, default=None):
    for p in path:
        try:
            o = o[p]
        except (KeyError, IndexError, TypeError):
            return default
    return o


def txt(d):
    if not d:
        return ""
    if isinstance(d, str):
        return d
    if "simpleText" in d:
        return d["simpleText"]
    if "runs" in d:
        return "".join(r.get("text", "") for r in d["runs"])
    return d.get("content", "")


def parse_dur(s):
    try:
        secs = 0
        for p in s.split(":"):
            secs = secs * 60 + int(p)
        return secs
    except ValueError:
        return 0


def vthumb(vid):
    return f"https://i.ytimg.com/vi/{vid}/mqdefault.jpg"


def fix_url(u):
    return ("https:" + u) if u and u.startswith("//") else (u or "")


URL_RE = re.compile(r'((?:https?://|www\.)[^\s<>"\']+)')


def linkify(text):
    """Escape text for Pango markup and turn URLs into clickable links."""
    out = []
    for i, part in enumerate(URL_RE.split(text or "")):
        if i % 2 == 0:
            out.append(GLib.markup_escape_text(part))
            continue
        url, trail = part, ""
        while url and url[-1] in ".,;:!?)]}":
            trail = url[-1] + trail
            url = url[:-1]
        href = url if url.startswith("http") else "http://" + url
        out.append(f'<a href="{GLib.markup_escape_text(href)}">'
                   f'{GLib.markup_escape_text(url)}</a>'
                   f'{GLib.markup_escape_text(trail)}')
    return "".join(out)


def style_sub(btn, subscribed):
    """Subscribe = red, Unsubscribe = gray."""
    btn.set_label("Unsubscribe" if subscribed else "Subscribe")
    btn.remove_css_class("tube-sub")
    btn.remove_css_class("tube-unsub")
    btn.add_css_class("tube-unsub" if subscribed else "tube-sub")


def parse_items(data):
    """Pull videos, shorts, channels and community posts out of any InnerTube reply."""
    out, seen = [], set()

    def add(it):
        key = (it["kind"], it["id"])
        if it["id"] and key not in seen:
            seen.add(key)
            out.append(it)

    for n in walk(data):
        if "videoRenderer" in n:
            v = n["videoRenderer"]
            owner = v.get("ownerText") or v.get("longBylineText") or {}
            length = txt(v.get("lengthText"))
            add({"kind": "video", "id": v.get("videoId"),
                 "title": txt(v.get("title")), "channel": txt(owner),
                 "channel_id": dig(owner, "runs", 0, "navigationEndpoint",
                                   "browseEndpoint", "browseId", default=""),
                 "dur": parse_dur(length), "length": length,
                 "desc": txt(dig(v, "detailedMetadataSnippets", 0, "snippetText"))
                         or txt(v.get("descriptionSnippet")),
                 "meta": " · ".join(x for x in (
                     txt(v.get("viewCountText")),
                     txt(v.get("publishedTimeText"))) if x),
                 "thumb": vthumb(v.get("videoId"))})
        elif "lockupViewModel" in n:
            lv = n["lockupViewModel"]
            if lv.get("contentType") != "LOCKUP_CONTENT_TYPE_VIDEO":
                continue
            rows = dig(lv, "metadata", "lockupMetadataViewModel", "metadata",
                       "contentMetadataViewModel", "metadataRows", default=[])
            parts = [[dig(p, "text", "content", default="")
                      for p in r.get("metadataParts", [])] for r in rows]
            length = ""
            for m in walk(lv.get("contentImage")):
                if "thumbnailBadgeViewModel" in m:
                    length = dig(m, "thumbnailBadgeViewModel", "text", default="")
                    break
            add({"kind": "video", "id": lv.get("contentId"),
                 "title": dig(lv, "metadata", "lockupMetadataViewModel",
                              "title", "content", default=""),
                 "channel": parts[0][0] if parts and parts[0] else "",
                 "channel_id": "", "dur": parse_dur(length), "length": length,
                 "desc": "", "meta": " · ".join(sum(parts[1:], [])),
                 "thumb": vthumb(lv.get("contentId"))})
        elif "shortsLockupViewModel" in n:
            s = n["shortsLockupViewModel"]
            vid = dig(s, "onTap", "innertubeCommand", "reelWatchEndpoint",
                      "videoId") or dig(s, "inlinePlayerData", "onVisible",
                                        "innertubeCommand", "watchEndpoint",
                                        "videoId")
            add({"kind": "short", "id": vid,
                 "title": dig(s, "overlayMetadata", "primaryText", "content",
                              default=""),
                 "channel": "", "channel_id": "",
                 "meta": dig(s, "overlayMetadata", "secondaryText", "content",
                             default=""), "thumb": vthumb(vid)})
        elif "reelItemRenderer" in n:
            s = n["reelItemRenderer"]
            add({"kind": "short", "id": s.get("videoId"),
                 "title": txt(s.get("headline")), "channel": "",
                 "channel_id": "", "meta": txt(s.get("viewCountText")),
                 "thumb": vthumb(s.get("videoId"))})
        elif "channelRenderer" in n or "gridChannelRenderer" in n:
            c = n.get("channelRenderer") or n.get("gridChannelRenderer")
            th = dig(c, "thumbnail", "thumbnails", -1, "url", default="")
            add({"kind": "channel", "id": c.get("channelId"),
                 "title": txt(c.get("title")), "channel": txt(c.get("title")),
                 "channel_id": c.get("channelId"),
                 "meta": " · ".join(x for x in (
                     txt(c.get("subscriberCountText")),
                     txt(c.get("videoCountText"))) if x),
                 "desc": txt(c.get("descriptionSnippet")),
                 "thumb": fix_url(th)})
        elif "backstagePostThreadRenderer" in n:
            p = dig(n, "backstagePostThreadRenderer", "post",
                    "backstagePostRenderer")
            if not p:
                continue
            img = dig(p, "backstageAttachment", "backstageImageRenderer",
                      "image", "thumbnails", -1, "url", default="")
            likes = txt(p.get("voteCount"))
            add({"kind": "post", "id": p.get("postId"),
                 "title": txt(p.get("authorText")),
                 "channel": txt(p.get("authorText")), "channel_id": "",
                 "body": txt(p.get("contentText")),
                 "meta": " · ".join(x for x in (
                     txt(p.get("publishedTimeText")),
                     f"{likes} likes" if likes else "") if x),
                 "thumb": img})
    return out


def channel_avatar(data):
    return fix_url(dig(data, "metadata", "channelMetadataRenderer", "avatar",
                       "thumbnails", 0, "url", default=""))


def channel_header(data):
    """Banner, avatar, name, handle, subscriber / video counts of a channel."""
    h = {"banner": "", "avatar": channel_avatar(data),
         "name": dig(data, "metadata", "channelMetadataRenderer", "title",
                     default=""),
         "handle": "", "subs": "", "videos": "",
         "desc": dig(data, "metadata", "channelMetadataRenderer", "description",
                     default="")}
    c4 = dig(data, "header", "c4TabbedHeaderRenderer")
    if c4:  # older header layout
        h["banner"] = fix_url(dig(c4, "banner", "thumbnails", -1, "url",
                                  default=""))
        h["avatar"] = fix_url(dig(c4, "avatar", "thumbnails", -1, "url",
                                  default="")) or h["avatar"]
        h["subs"] = txt(c4.get("subscriberCountText"))
        h["videos"] = txt(c4.get("videosCountText"))
        h["handle"] = txt(c4.get("channelHandleText"))
    pvm = dig(data, "header", "pageHeaderRenderer", "content",
              "pageHeaderViewModel")
    if pvm:  # current header layout
        h["banner"] = fix_url(dig(pvm, "banner", "imageBannerViewModel", "image",
                                  "sources", -1, "url", default="")) \
            or h["banner"]
        h["avatar"] = fix_url(dig(pvm, "image", "decoratedAvatarViewModel",
                                  "avatar", "avatarViewModel", "image",
                                  "sources", -1, "url", default="")) \
            or h["avatar"]
        h["name"] = dig(pvm, "title", "dynamicTextViewModel", "text", "content",
                        default="") or h["name"]
        h["desc"] = dig(pvm, "description", "descriptionPreviewViewModel",
                        "description", "content", default="") or h["desc"]
        rows = dig(pvm, "metadata", "contentMetadataViewModel", "metadataRows",
                   default=[])
        for r in rows:
            for p in r.get("metadataParts", []):
                t = dig(p, "text", "content", default="")
                low = t.lower()
                if t.startswith("@"):
                    h["handle"] = t
                elif "subscriber" in low:
                    h["subs"] = t
                elif "video" in low:
                    h["videos"] = t
    return h


def remember_avatar(cid, url):
    if cid and url and AVATARS.get(cid) != url:
        AVATARS[cid] = url
        try:
            jsave(AVATARS_FILE, AVATARS)
        except OSError:
            pass


def ensure_avatars(ids, limit=40):
    """Fetch (and cache) the avatar of channels we don't have one for yet."""
    missing = [c for c in ids if c not in AVATARS][:limit]

    def one(cid):
        try:
            remember_avatar(cid, channel_avatar(innertube("browse", browseId=cid)))
        except Exception:  # noqa: BLE001
            pass
    if missing:
        with ThreadPoolExecutor(6) as ex:
            list(ex.map(one, missing))


def channel_fetch(cid, tab_names, header_out=None):
    """Return (channel name, items) for a channel tab (e.g. videos / posts).

    If `header_out` is a dict it is filled with banner / avatar / counts.
    """
    home = innertube("browse", browseId=cid)
    name = dig(home, "metadata", "channelMetadataRenderer", "title", default="")
    remember_avatar(cid, channel_avatar(home))
    if header_out is not None:
        header_out.update(channel_header(home))
    data = home
    for n in walk(home):
        t = n.get("tabRenderer")
        if t and t.get("title", "").lower() in tab_names:
            p = dig(t, "endpoint", "browseEndpoint", "params")
            if p:
                data = innertube("browse", browseId=cid, params=p)
                break
    return name, parse_items(data)


def watch_details(vid):
    """One 'next' call: related videos + title/channel/description of the video."""
    data = innertube("next", videoId=vid)
    out = {"related": [i for i in parse_items(data)
                       if i["kind"] == "video" and i["id"] != vid]}
    for n in walk(data):
        if "videoPrimaryInfoRenderer" in n:
            p = n["videoPrimaryInfoRenderer"]
            out["title"] = txt(p.get("title"))
            out["views"] = txt(dig(p, "viewCount", "videoViewCountRenderer",
                                   "viewCount"))
            out["date"] = txt(p.get("dateText"))
        elif "videoSecondaryInfoRenderer" in n:
            s = n["videoSecondaryInfoRenderer"]
            out["desc"] = (dig(s, "attributedDescription", "content")
                           or txt(s.get("description")))
        elif "videoOwnerRenderer" in n:
            o = n["videoOwnerRenderer"]
            out["channel"] = txt(o.get("title"))
            out["channel_id"] = dig(o, "navigationEndpoint", "browseEndpoint",
                                    "browseId", default="")
    out["comment_token"] = comment_token(data)
    return out


def _first_token(o):
    for m in walk(o):
        t = dig(m, "continuationCommand", "token")
        if t:
            return t
    return None


def comment_token(data):
    """Continuation token that loads the first page of comments."""
    for n in walk(data):
        sec = n.get("itemSectionRenderer")
        if sec and (sec.get("sectionIdentifier") == "comment-item-section"
                    or sec.get("targetId") == "comments-section"):
            t = _first_token(sec)
            if t:
                return t
    return None


def _comment_from_payload(p):
    a, pr, tb = p.get("author", {}), p.get("properties", {}), p.get("toolbar", {})
    likes = tb.get("likeCountNotliked") or tb.get("likeCountLiked") or ""
    return {"author": a.get("displayName", ""), "avatar": fix_url(
                a.get("avatarThumbnailUrl", "")),
            "text": dig(pr, "content", "content", default=""),
            "time": pr.get("publishedTime", ""),
            "likes": "" if likes in ("0", 0) else str(likes),
            "reply_count": str(tb.get("replyCount") or ""), "reply_token": None}


def _comment_from_renderer(r):
    if not r:
        return None
    return {"author": txt(r.get("authorText")),
            "avatar": fix_url(dig(r, "authorThumbnail", "thumbnails", -1, "url",
                                  default="")),
            "text": txt(r.get("contentText")),
            "time": txt(r.get("publishedTimeText")),
            "likes": txt(r.get("voteCount")),
            "reply_count": str(r.get("replyCount") or ""), "reply_token": None}


def parse_comments(data, replies=False):
    """Return {"items": [...], "token": next-page token, "count": "1,234"}."""
    ents = {}
    for n in walk(data):
        p = n.get("commentEntityPayload")
        if p:
            ents[p.get("key")] = p
    for mu in dig(data, "frameworkUpdates", "entityBatchUpdate", "mutations",
                  default=[]):
        p = dig(mu, "payload", "commentEntityPayload")
        if p:
            ents[mu.get("entityKey")] = p
    items, count = [], ""
    for n in walk(data):
        if "commentsHeaderRenderer" in n and not count:
            count = txt(dig(n, "commentsHeaderRenderer", "commentsCount"))
        if replies:
            vm = n.get("commentViewModel")
            c = None
            if isinstance(vm, dict) and vm.get("commentKey"):
                p = ents.get(vm["commentKey"])
                c = _comment_from_payload(p) if p else None
            elif "commentRenderer" in n:
                c = _comment_from_renderer(n["commentRenderer"])
            if c:
                items.append(c)
        else:
            t = n.get("commentThreadRenderer")
            if t:
                vm = dig(t, "commentViewModel", "commentViewModel") or {}
                p = ents.get(vm.get("commentKey"))
                c = (_comment_from_payload(p) if p else
                     _comment_from_renderer(dig(t, "comment", "commentRenderer")))
                if c:
                    c["reply_token"] = _first_token(t.get("replies"))
                    items.append(c)
    token = None
    for e in data.get("onResponseReceivedEndpoints") or []:
        its = (dig(e, "reloadContinuationItemsCommand", "continuationItems")
               or dig(e, "appendContinuationItemsAction", "continuationItems")
               or [])
        for it in its:
            if "continuationItemRenderer" in it:
                token = _first_token(it["continuationItemRenderer"]) or token
    return {"items": items, "token": token, "count": count}


def missing_codecs():
    """Names of codecs the in-app player needs that GStreamer can't decode."""
    try:
        gi.require_version("Gst", "1.0")
        from gi.repository import Gst
        Gst.init(None)
    except Exception:  # noqa: BLE001
        return []
    needs = (
        (("avdec_h264", "openh264dec"), "H.264"),
        (("avdec_aac",), "AAC"),
    )
    return [name for factories, name in needs
            if not any(Gst.ElementFactory.find(factory)
                       for factory in factories)]


def available_gstreamer_codecs():
    """Return codecs with an installed GStreamer decoder."""
    gi.require_version("Gst", "1.0")
    from gi.repository import Gst
    Gst.init(None)

    def has_decoder(*names):
        return any(Gst.ElementFactory.find(name) for name in names)

    hardware_h264 = ("vah264dec", "vaapih264dec", "nvh264dec") if HWDEC else ()
    available = set()
    if has_decoder("avdec_h264", "openh264dec",
                   *hardware_h264):
        available.add("h264")
    decoder_factories = {
        "vp9": ("vp9dec", "avdec_vp9", "vavp9dec", "vaapivp9dec", "nvvp9dec")
        if HWDEC else ("vp9dec", "avdec_vp9"),
        "av1": ("dav1d", "av1dec", "avdec_av1", "libaom-av1dec", "vaav1dec",
                "nvav1dec")
        if HWDEC else ("dav1d", "av1dec", "avdec_av1", "libaom-av1dec"),
        "aac": ("avdec_aac",),
        "opus": ("opusdec", "avdec_opus"),
        "vorbis": ("vorbisdec", "avdec_vorbis"),
        "mp3": ("mpg123audiodec", "avdec_mp3"),
    }
    available.update(codec for codec, factories in decoder_factories.items()
                     if has_decoder(*(factory.strip()
                                      for factory in factories)))
    return available


HW_DECODER_PREFIXES = ("va", "nv", "qsv", "msdk", "v4l2", "d3d", "amf", "vk",
                       "omx", "vtdec", "mf")


def tame_gst_decoders():
    """Rank EVERY hardware video decoder (VA, NVDEC incl. the *sl* stateless
    ones, QSV, MSDK, V4L2...) at NONE so GStreamer uses the software decoders
    (libvpx / dav1d / libav). The old fixed name list missed several, and a
    hardware decoder picked for VP9 / AV1 gives audio or a single frame and
    then nothing. Set GTKTUBE_HWDEC=1 to keep them."""
    if HWDEC:
        return
    try:
        gi.require_version("Gst", "1.0")
        from gi.repository import Gst
        Gst.init(None)
        features = Gst.Registry.get().get_feature_list(Gst.ElementFactory)
    except Exception as exc:  # noqa: BLE001
        dlog("could not inspect GStreamer registry:", exc)
        return
    off, soft = [], []
    for f in features:
        try:
            klass = f.get_metadata("klass") or ""
            if "Decoder" not in klass or "Video" not in klass:
                continue
            name = f.get_name()
            if name.startswith(HW_DECODER_PREFIXES):
                if f.get_rank() > 0:
                    f.set_rank(0)
                    off.append(name)
            elif f.get_rank() > 0:
                soft.append(f"{name}:{f.get_rank()}")
        except Exception:  # noqa: BLE001
            continue
    dlog("hardware video decoders disabled:", sorted(off) or "none found")
    dlog("software video decoders in use:", sorted(soft))


def describe_formats(info):
    """One-line summary per video format, for GTKTUBE_DEBUG output."""
    parts = []
    for f in info.get("formats", []):
        if str(f.get("vcodec") or "none") == "none" or not f.get("height"):
            continue
        parts.append(
            f"{f.get('height')}p{int(f.get('fps') or 0)}/"
            f"{str(f.get('vcodec'))[:4]}/{f.get('dynamic_range', 'SDR')}/"
            f"{f.get('__yt_dlp_client', '?')}/"
            f"{'url' if f.get('url') else 'NOURL'}")
    return ", ".join(parts) or "(no video formats)"


def account_info():
    """Name / handle / photo of the signed-in Google account (or None)."""
    attempts = (("account/account_menu", {}),
                ("account/accounts_list",
                 {"accountReadMask": {"returnOwner": True,
                                      "returnBrandAccounts": True,
                                      "returnPersonaAccounts": False}}))
    for ep, body in attempts:
        try:
            data = innertube(ep, **body)
        except Exception:  # noqa: BLE001
            continue
        for n in walk(data):
            h = n.get("activeAccountHeaderRenderer")
            if h:
                return {"name": txt(h.get("accountName")),
                        "handle": txt(h.get("channelHandle")),
                        "photo": fix_url(dig(h, "accountPhoto", "thumbnails", -1,
                                             "url", default=""))}
            a = n.get("accountItem")
            if a and a.get("isSelected"):
                return {"name": txt(a.get("accountName")),
                        "handle": txt(a.get("accountByline")),
                        "photo": fix_url(dig(a, "accountPhoto", "thumbnails", -1,
                                             "url", default=""))}
    return None


def run_async(fn, cb):
    def w():
        try:
            r, e = fn(), None
        except Exception as ex:  # noqa: BLE001
            r, e = None, ex
        GLib.idle_add(lambda: (cb(r, e), False)[1])
    threading.Thread(target=w, daemon=True).start()


_thumb_pool = ThreadPoolExecutor(6)
_thumb_cache = {}


def load_thumb(url, picture, on_fail=None):
    """Load an image into `picture`. `on_fail` is called if it can't be loaded."""
    if not url:
        return

    def fetch():
        if url not in _thumb_cache:
            last = None
            for _ in range(2):  # one retry for transient network errors
                try:
                    req = urllib.request.Request(url, headers={"User-Agent": UA})
                    with urllib.request.urlopen(req, timeout=15) as r:
                        _thumb_cache[url] = r.read()
                    break
                except urllib.error.HTTPError as e:
                    last = e
                    if e.code in (400, 403, 404, 410):
                        break
                except Exception as e:  # noqa: BLE001
                    last = e
            else:
                pass
            if url not in _thumb_cache:
                raise last or RuntimeError("thumbnail failed")
        return _thumb_cache[url]

    def done(f):
        try:
            data = f.result()
        except Exception:  # noqa: BLE001
            if on_fail:
                GLib.idle_add(lambda: (on_fail(), False)[1])
            return

        def apply():
            try:
                picture.set_paintable(
                    Gdk.Texture.new_from_bytes(GLib.Bytes.new(data)))
            except GLib.Error:
                if on_fail:
                    on_fail()
            return False
        GLib.idle_add(apply)

    _thumb_pool.submit(fetch).add_done_callback(done)


# ------------------------------------------------------------------ widgets


def label(text, css=None, lines=0, xalign=0.0):
    l = Gtk.Label(label=text, xalign=xalign, wrap=True)
    l.set_max_width_chars(34)
    if lines:
        l.set_lines(lines)
        l.set_ellipsize(3)  # Pango.EllipsizeMode.END
    if css:
        l.add_css_class(css)
    return l


def collapse(widget):
    """Remove a widget (and its FlowBox wrapper) from layout: no empty gap."""
    widget.set_visible(False)
    p = widget.get_parent()
    if isinstance(p, Gtk.FlowBoxChild):
        p.set_visible(False)


def thumb_widget(item, pic):
    """Wrap a Picture in an overlay with a duration badge when we know it."""
    if item["kind"] == "video" and item.get("length"):
        ov = Gtk.Overlay(child=pic, halign=Gtk.Align.START, valign=Gtk.Align.START)
        ov.add_css_class("tube-thumbbox")
        ov.set_overflow(Gtk.Overflow.HIDDEN)
        b = Gtk.Label(label=item["length"], halign=Gtk.Align.END,
                      valign=Gtk.Align.END, margin_end=6, margin_bottom=6)
        b.add_css_class("tube-badge")
        ov.add_overlay(b)
        return ov
    return pic


def new_picture(kind):
    pic = Gtk.Picture(content_fit=Gtk.ContentFit.COVER, can_shrink=True,
                      halign=Gtk.Align.START, valign=Gtk.Align.START)
    pic.add_css_class("tube-thumb")
    if kind == "channel":
        pic.add_css_class("tube-avatar")
        pic.set_overflow(Gtk.Overflow.HIDDEN)
    return pic


def avatar_widget(size):
    """Round picture of an exact size, whatever the source image's own size.

    The picture is an overlay child, and overlay children don't take part in
    the size measurement, so the image's intrinsic size can't stretch it.
    """
    pic = Gtk.Picture(content_fit=Gtk.ContentFit.COVER, can_shrink=True)
    pic.add_css_class("tube-thumb")
    ov = Gtk.Overlay(child=Gtk.Box(width_request=size, height_request=size),
                     halign=Gtk.Align.START, valign=Gtk.Align.START)
    ov.add_overlay(pic)
    ov.set_clip_overlay(pic, True)
    ov.set_overflow(Gtk.Overflow.HIDDEN)
    ov.add_css_class("tube-avatar")
    ov.set_size_request(size, size)
    return ov, pic


def click(widget, item, on_open):
    g = Gtk.GestureClick()
    g.connect("released", lambda *_: on_open(item))
    widget.add_controller(g)
    widget.set_cursor(Gdk.Cursor.new_from_name("pointer"))
    if item.get("kind") in ("video", "short") and item.get("id"):
        # hovering a video for a moment resolves its streams in the background,
        # so clicking it starts playing much sooner
        state = {"t": 0}

        def fire():
            state["t"] = 0
            prefetch_info(item["id"])
            return False

        def enter(*_):
            if state["t"]:
                GLib.source_remove(state["t"])
            state["t"] = GLib.timeout_add(150, fire)

        def leave(*_):
            if state["t"]:
                GLib.source_remove(state["t"])
                state["t"] = 0
        m = Gtk.EventControllerMotion()
        m.connect("enter", enter)
        m.connect("leave", leave)
        widget.add_controller(m)


def make_card(item, on_open):
    """Vertical card for grids and shelves."""
    kind = item["kind"]
    card = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6,
                   valign=Gtk.Align.START)
    card.add_css_class("tube-card")
    pic = new_picture(kind)
    avw = None
    if kind == "channel":
        avw, pic = avatar_widget(88)
    labels = []
    if kind != "post" or item.get("thumb"):
        w = avw or thumb_widget(item, pic)
        if kind == "channel":
            w.set_halign(Gtk.Align.CENTER)
        card.append(w)
        # a video whose thumbnail doesn't exist is gone: don't leave a hole
        load_thumb(item.get("thumb"), pic,
                   (lambda: collapse(card)) if kind in ("video", "short") else None)
    if kind == "post":
        labels += [label(item["title"], "tube-title"),
                   label(item.get("body", ""), None, lines=10),
                   label(item["meta"], "tube-meta")]
        labels[1].set_max_width_chars(70)
    else:
        align = 0.5 if kind == "channel" else 0.0
        labels.append(label(item["title"], "tube-title", lines=2, xalign=align))
        if item.get("channel") and kind != "channel":
            labels.append(label(item["channel"], "tube-meta", lines=1))
        if item.get("meta"):
            labels.append(label(item["meta"], "tube-meta", lines=1, xalign=align))
    for l in labels:
        card.append(l)

    def resize(cw):
        inner = max(60, cw - 12)
        card.set_size_request(cw, -1)
        for l in labels:
            l.set_size_request(inner, -1)
        if kind == "video":
            pic.set_size_request(inner, inner * 9 // 16)
        elif kind == "short":
            pic.set_size_request(inner, inner * 16 // 9)
        elif kind == "channel":
            pic.set_size_request(88, 88)
        elif kind == "post":
            pic.set_size_request(inner, min(inner * 9 // 16, 380))
    card._resize = resize
    resize(264)
    click(card, item, on_open)
    return card


def make_row(item, on_open):
    """Horizontal YouTube-style search result row."""
    kind = item["kind"]
    row = Gtk.Box(spacing=14, valign=Gtk.Align.START)
    row.add_css_class("tube-card")
    pic = new_picture(kind)
    w = None
    if kind == "channel":
        w, pic = avatar_widget(88)
        w.set_valign(Gtk.Align.CENTER)
    else:
        w = thumb_widget(item, pic)
    row.append(w)
    load_thumb(item.get("thumb"), pic,
               (lambda: collapse(row)) if kind in ("video", "short") else None)
    text = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4,
                   valign=Gtk.Align.START if kind != "channel" else Gtk.Align.CENTER)
    labels = [label(item["title"], "tube-title-big", lines=2)]
    if item.get("meta"):
        labels.append(label(item["meta"], "tube-meta", lines=1))
    if item.get("channel") and kind != "channel":
        labels.append(label(item["channel"], "tube-meta", lines=1))
    if item.get("desc"):
        labels.append(label(item["desc"], "tube-meta", lines=2))
    for l in labels:
        l.set_max_width_chars(100)
        text.append(l)
    row.append(text)

    def resize(rw):
        tw = 88 if kind == "channel" else min(360, int(rw * 0.38))
        pic.set_size_request(tw, 88 if kind == "channel" else tw * 9 // 16)
        tx = max(100, rw - tw - 14 - 12)
        for l in labels:
            l.set_size_request(tx, -1)
        row.set_size_request(rw, -1)
    row._resize = resize
    resize(700)
    click(row, item, on_open)
    return row


def make_shelf(title, icon, items, on_open, card_w):
    box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8)
    box.add_css_class("tube-shelf")
    head = Gtk.Box(spacing=8)
    head.append(Gtk.Image(icon_name=icon))
    l = Gtk.Label(label=title)
    l.add_css_class("title-4")
    head.append(l)
    strip = Gtk.Box(spacing=10)
    for it in items:
        c = make_card(it, on_open)
        c._resize(card_w)
        strip.append(c)
    sc = Gtk.ScrolledWindow(child=strip, vscrollbar_policy=Gtk.PolicyType.NEVER,
                            hscrollbar_policy=Gtk.PolicyType.AUTOMATIC,
                            propagate_natural_height=True)
    box.append(head)
    box.append(sc)
    return box


class ItemGrid(Gtk.Box):
    """Results container.

    mode="grid": responsive cards (`target` columns when wide, fewer when narrow)
    mode="list": YouTube-style search rows (thumbnail left, text right)
    Shorts are never mixed in: they get their own horizontal shelf.
    Entries without an id/title are dropped, and entries whose thumbnail can't
    be loaded collapse, so the layout never contains empty holes.
    """

    def __init__(self, on_open, mode="grid", target=4, min_w=240, max_w=0,
                 fixed_w=0, extra_pad=14, shorts_in_shelf=True):
        super().__init__(orientation=Gtk.Orientation.VERTICAL, spacing=8,
                         margin_top=6, margin_bottom=12,
                         margin_start=12, margin_end=12)
        self.on_open, self.mode, self.target, self.min_w = on_open, mode, target, min_w
        self.max_w, self.fixed_w, self.extra_pad = max_w, fixed_w, extra_pad
        self.status = Gtk.Label(wrap=True, visible=False, vexpand=True,
                                halign=Gtk.Align.CENTER, valign=Gtk.Align.CENTER)
        self.spinner = Gtk.Spinner(visible=False, width_request=40,
                                   height_request=40, vexpand=True,
                                   halign=Gtk.Align.CENTER,
                                   valign=Gtk.Align.CENTER, margin_top=36,
                                   margin_bottom=36)
        self.body = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=18)
        for w in (self.spinner, self.status, self.body):
            self.append(w)
        self.loaded = False
        self.items = []
        self._gen = 0
        self._w = 0
        self.cards, self.rows, self.flows = [], [], []
        self.add_tick_callback(self._tick)

    # --- sizing
    def _tick(self, *_):
        if self.cards or self.rows:
            if self.fixed_w:
                w = self.fixed_w
            else:
                sw = self.get_ancestor(Gtk.ScrolledWindow)
                w = sw.get_width() if sw else 0
            if w and w != self._w:
                self._w = w
                self._layout(w)
        return GLib.SOURCE_CONTINUE

    def _layout(self, w):
        avail = w - self.get_margin_start() - self.get_margin_end() - \
            (0 if self.fixed_w else self.extra_pad)
        if self.mode == "list":
            rw = min(avail, self.max_w) if self.max_w else avail
            for r in self.rows:
                r._resize(rw)
            return
        cols = max(1, min(self.target, (avail + 8) // (self.min_w + 8)))
        cw = (avail - 8 * (cols - 1)) // cols - 2
        if self.max_w:
            cw = min(cw, self.max_w)
        for f in self.flows:
            f.set_min_children_per_line(cols)
            f.set_max_children_per_line(cols)
        for c in self.cards:
            c._resize(cw)

    # --- content
    def clear(self):
        self.cards, self.rows, self.flows = [], [], []
        while (c := self.body.get_first_child()):
            self.body.remove(c)

    def _flow(self, items):
        if not items:
            return
        f = Gtk.FlowBox(selection_mode=Gtk.SelectionMode.NONE, homogeneous=False,
                        valign=Gtk.Align.START, column_spacing=8, row_spacing=14,
                        min_children_per_line=1,
                        max_children_per_line=self.target)
        for it in items:
            c = make_card(it, self.on_open)
            self.cards.append(c)
            f.append(c)
        self.flows.append(f)
        self.body.append(f)

    def _rows(self, items, parent):
        for it in items:
            r = make_row(it, self.on_open)
            self.rows.append(r)
            parent.append(r)

    def set_items(self, items, empty_msg="Nothing here."):
        self.clear()
        # drop broken entries (no id / nothing to show) so they leave no gap
        items = [i for i in items
                 if i.get("id") and (i.get("title") or i.get("body"))]
        self.items = items
        self._set_status("" if items else empty_msg)
        shorts = [i for i in items if i["kind"] == "short"]
        chans = [i for i in items if i["kind"] == "channel"]
        rest = [i for i in items if i["kind"] not in ("short", "channel")]
        shelf = (make_shelf("Shorts", "camera-video-symbolic", shorts[:8],
                            self.on_open, 150) if shorts else None)
        if not rest and not chans and shorts:  # the dedicated Shorts page
            self._flow(shorts)
        elif self.mode == "list":
            col = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=14,
                          halign=Gtk.Align.CENTER)
            self._rows(chans[:2], col)
            self._rows(rest[:5], col)
            if shelf:
                col.append(shelf)
            self._rows(rest[5:], col)
            self.body.append(col)
        else:
            if chans:
                self.body.append(make_shelf("Channels", "avatar-default-symbolic",
                                            chans, self.on_open, 150))
            self._flow(rest[:8])
            if shelf:
                self.body.append(shelf)
            self._flow(rest[8:])
        self._w = 0  # force relayout on next frame

    def _set_status(self, text):
        self.status.set_text(text)
        self.status.set_visible(bool(text))

    def load(self, fn, empty_msg="Nothing here."):
        self._gen += 1
        gen = self._gen
        self.clear()
        self._set_status("")
        self.spinner.set_visible(True)
        self.spinner.start()

        def done(items, err):
            if gen != self._gen:
                return
            self.spinner.stop()
            self.spinner.set_visible(False)
            if err:
                self._set_status(f"Error: {err}")
            else:
                self.loaded = True
                self.set_items(items, empty_msg)
        run_async(fn, done)


def scrolled(child):
    return Gtk.ScrolledWindow(child=child, hexpand=True, vexpand=True,
                              hscrollbar_policy=Gtk.PolicyType.EXTERNAL)


class CommentRow(Gtk.Box):
    def __init__(self, c, reply=False):
        super().__init__(spacing=12)
        self.c, self.loaded = c, False
        av, pic = avatar_widget(28 if reply else 40)
        load_thumb(c.get("avatar"), pic)
        col = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=3, hexpand=True)
        head = Gtk.Label(xalign=0, wrap=True)
        head.set_markup(f"<b>{GLib.markup_escape_text(c['author'])}</b>  "
                        f"<span alpha='60%'>{GLib.markup_escape_text(c['time'])}</span>")
        body = Gtk.Label(xalign=0, wrap=True, selectable=True,
                         wrap_mode=Pango.WrapMode.WORD_CHAR)
        body.set_markup(linkify(c["text"]))
        body.set_max_width_chars(100)
        foot = Gtk.Box(spacing=10)
        if c.get("likes"):
            lk = Gtk.Label(label=f"👍 {c['likes']}")
            lk.add_css_class("tube-meta")
            foot.append(lk)
        for w in (head, body, foot):
            col.append(w)
        self.rbox = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=10,
                            margin_top=6, visible=False)
        self.rmore = None
        if c.get("reply_token"):
            n = c.get("reply_count")
            self.rtext = (f"{n} repl{'y' if n == '1' else 'ies'}" if n
                          else "Replies")
            self.rbtn = Gtk.Button(label="▸ " + self.rtext, halign=Gtk.Align.START)
            self.rbtn.add_css_class("flat")
            self.rbtn.connect("clicked", self.toggle)
            foot.append(self.rbtn)
        col.append(self.rbox)
        self.append(av)
        self.append(col)

    def toggle(self, *_):
        if self.rbox.get_visible():
            self.rbox.set_visible(False)
            self.rbtn.set_label("▸ " + self.rtext)
            return
        self.rbox.set_visible(True)
        self.rbtn.set_label("▾ Hide replies")
        if not self.loaded:
            self.loaded = True
            self.load_replies(self.c["reply_token"])

    def load_replies(self, tok):
        if self.rmore:
            self.rbox.remove(self.rmore)
            self.rmore = None
        hint = Gtk.Label(label="Loading replies…", xalign=0)
        hint.add_css_class("tube-meta")
        self.rbox.append(hint)

        def done(r, e):
            self.rbox.remove(hint)
            if e:
                self.loaded = False
                self.rbox.append(Gtk.Label(label=f"Could not load replies: {e}",
                                           xalign=0))
                return
            for rc in r["items"]:
                self.rbox.append(CommentRow(rc, reply=True))
            if r["token"]:
                self.rmore = Gtk.Button(label="Show more replies",
                                        halign=Gtk.Align.START)
                self.rmore.add_css_class("flat")
                self.rmore.connect("clicked", lambda *_: self.load_replies(r["token"]))
                self.rbox.append(self.rmore)
        run_async(lambda: parse_comments(innertube("next", continuation=tok),
                                         replies=True), done)


class CommentsSection(Gtk.Box):
    def __init__(self):
        super().__init__(orientation=Gtk.Orientation.VERTICAL, spacing=12,
                         margin_top=12)
        self.head = Gtk.Label(label="Comments", xalign=0)
        self.head.add_css_class("title-4")
        self.status = Gtk.Label(xalign=0)
        self.status.add_css_class("tube-meta")
        self.list = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=16)
        self.more = Gtk.Button(label="Show more comments", halign=Gtk.Align.START,
                               visible=False)
        self.more.connect("clicked", lambda *_: self._fetch())
        for w in (self.head, self.status, self.list, self.more):
            self.append(w)
        self.gen, self.token, self.count = 0, None, ""

    def clear(self):
        self.gen += 1
        self.token, self.count = None, ""
        while (c := self.list.get_first_child()):
            self.list.remove(c)
        self.head.set_text("Comments")
        self.status.set_text("")
        self.more.set_visible(False)

    def start(self, token):
        self.clear()
        self.token = token
        if not token:
            self.status.set_text("Comments are unavailable or turned off.")
            return
        self.status.set_text("Loading comments…")
        self._fetch()

    def _fetch(self):
        tok, gen = self.token, self.gen
        self.more.set_sensitive(False)
        run_async(lambda: parse_comments(innertube("next", continuation=tok)),
                  lambda r, e: self._done(gen, r, e))

    def _done(self, gen, r, e):
        if gen != self.gen:
            return
        self.more.set_sensitive(True)
        if e:
            self.status.set_text(f"Could not load comments: {e}")
            return
        if r["count"] and not self.count:
            self.count = r["count"]
            self.head.set_text(f"{self.count} Comments")
        for c in r["items"]:
            self.list.append(CommentRow(c))
        self.token = r["token"]
        self.more.set_visible(bool(self.token))
        self.status.set_text("" if self.list.get_first_child() else "No comments.")


class PlayerBox(Gtk.Overlay):
    """Player area: a video/web stack with loading and playback overlays."""

    def __init__(self):
        super().__init__(hexpand=True)
        self.stack = Gtk.Stack(hexpand=True)
        self.set_child(self.stack)
        self.osd = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6,
                           halign=Gtk.Align.CENTER, valign=Gtk.Align.START,
                           margin_top=36, visible=False)
        self.osd.add_css_class("tube-osd")
        self.osd.set_can_target(False)  # never steal clicks from the video
        self.osd_lbl = Gtk.Label()
        self.osd_bar = Gtk.ProgressBar()
        self.osd_bar.set_size_request(170, -1)
        self.osd.append(self.osd_lbl)
        self.osd.append(self.osd_bar)
        self.add_overlay(self.osd)
        self._osd_t = 0

    def add_named(self, widget, name):
        self.stack.add_named(widget, name)

    def set_visible_child_name(self, name):
        self.stack.set_visible_child_name(name)

    def show_osd(self, text, fraction=None):
        self.osd_lbl.set_text(text)
        self.osd_bar.set_visible(fraction is not None)
        if fraction is not None:
            self.osd_bar.set_fraction(max(0.0, min(1.0, fraction)))
        self.osd.set_visible(True)
        if self._osd_t:
            GLib.source_remove(self._osd_t)
        self._osd_t = GLib.timeout_add(1000, self._hide_osd)

    def _hide_osd(self):
        self._osd_t = 0
        self.osd.set_visible(False)
        return False


class WatchPage(Gtk.ScrolledWindow):
    """Player page.

    Videos play from a single stream selected by the app, so the YouTube
    player's adaptive Auto mode cannot change resolution underneath it.
    """

    def __init__(self, app):
        super().__init__(hexpand=True, vexpand=True,
                         hscrollbar_policy=Gtk.PolicyType.EXTERNAL)
        self.app = app
        self.item = None
        self.info = {}
        self.mode = None  # "embed" (loading) | "web" | "stream"
        self.gen = 0
        self.web = None
        self.short, self._ph = False, 0  # Shorts mode / its player height
        self._vsave = 0  # pending (debounced) save of the volume setting
        self._click_src = 0  # pending single-click (pause) timer
        outer = Gtk.Box(spacing=16, margin_top=12, margin_bottom=12,
                        margin_start=16, margin_end=16)
        self.outer, self._fs, self._fix_was = outer, False, False
        self.set_child(outer)
        left = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8, hexpand=True)
        self.left = left
        right = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8,
                        valign=Gtk.Align.START)
        right.set_size_request(RELATED_W, -1)
        outer.append(left)
        outer.append(right)

        # --- player area: mapped video, loading overlay, or web player
        self.player = PlayerBox()
        self.player.set_size_request(-1, 480)
        self.player.add_css_class("tube-player")
        self.player.set_overflow(Gtk.Overflow.HIDDEN)
        lbox = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=14,
                       halign=Gtk.Align.CENTER, valign=Gtk.Align.CENTER)
        self.spinner = Gtk.Spinner(width_request=32, height_request=32)
        self.status = Gtk.Label(wrap=True, max_width_chars=56,
                                justify=Gtk.Justification.CENTER)
        lbox.append(self.spinner)
        lbox.append(self.status)
        lbox.set_halign(Gtk.Align.CENTER)
        lbox.set_valign(Gtk.Align.CENTER)
        lbox.set_can_target(False)
        self.loading_overlay = lbox
        self.player.add_overlay(lbox)
        self.video = Gtk.Video(autoplay=True, hexpand=True)
        self._hide_video_native_controls(self.video)
        self._set_video_center_play_indicator_visible(True)
        self.video.connect("notify::media-stream",
                           self._video_media_stream_changed)
        self.player.add_named(self.video, "video")

        # --- controls bar (bottom of the player): play, time, seek bar,
        #     volume, quality, fullscreen. Fades out while playing.
        self.controls_row = Gtk.Box(spacing=8)
        self.controls_row.set_halign(Gtk.Align.FILL)
        self.controls_row.set_valign(Gtk.Align.END)
        self.controls_row.set_margin_start(10)
        self.controls_row.set_margin_end(10)
        self.controls_row.set_margin_bottom(10)
        self.controls_row.add_css_class("tube-playback-controls")
        self.controls_row.set_visible(False)
        self.play_btn = Gtk.Button(icon_name="media-playback-pause-symbolic")
        self.play_btn.set_tooltip_text("Pause")
        self.play_btn.connect("clicked", self._toggle_playback)
        self.controls_row.append(self.play_btn)
        self.current_time = Gtk.Label(label="0:00", width_chars=6)
        self.controls_row.append(self.current_time)
        self.timeline = Gtk.Scale.new_with_range(
            Gtk.Orientation.HORIZONTAL, 0, 1, 0.1)
        self.timeline.set_draw_value(False)
        self.timeline.set_hexpand(True)
        self.timeline.set_sensitive(False)
        # "change-value" fires only for user input (click / drag / keys on the
        # bar), never for the programmatic updates done while playing.
        self.timeline.connect("change-value", self._timeline_change_value)
        self.controls_row.append(self.timeline)
        self.duration_label = Gtk.Label(label="0:00", width_chars=6)
        self.controls_row.append(self.duration_label)
        self._muted, self._vol_updating = False, False
        self.vol_btn = Gtk.Button(icon_name="audio-volume-high-symbolic")
        self.vol_btn.set_tooltip_text("Mute / unmute")
        self.vol_btn.connect("clicked", self._toggle_mute)
        self.vol_scale = Gtk.Scale.new_with_range(
            Gtk.Orientation.HORIZONTAL, 0, 100, 1)
        self.vol_scale.set_draw_value(False)
        self.vol_scale.set_size_request(90, -1)
        self.vol_scale.set_value(app.settings.get("volume", 100))
        self.vol_scale.set_tooltip_text("Volume (Up / Down keys)")
        self.vol_scale.connect("value-changed", self._volume_scale_changed)
        self.quality = Gtk.DropDown.new_from_strings(["Screen fit"])
        self.quality.add_css_class("tube-quality")
        self.quality.set_tooltip_text("Video quality")
        self.quality.set_visible(False)
        self.quality.connect("notify::selected", self._quality_changed)
        self.fs_btn = Gtk.Button(icon_name="view-fullscreen-symbolic")
        self.fs_btn.set_tooltip_text("Fullscreen (F)")
        self.fs_btn.connect("clicked",
                            lambda *_: self.app.toggle_video_fullscreen())
        for w in (self.vol_btn, self.vol_scale, self.quality, self.fs_btn):
            self.controls_row.append(w)
        self.player.add_overlay(self.controls_row)
        self._ctl_src, self._over_ctl, self._last_xy = 0, False, None
        mot = Gtk.EventControllerMotion()
        mot.connect("motion", self._on_motion)
        self.player.add_controller(mot)
        cmot = Gtk.EventControllerMotion()
        cmot.connect("enter", lambda *_: setattr(self, "_over_ctl", True))
        cmot.connect("leave", lambda *_: setattr(self, "_over_ctl", False))
        self.controls_row.add_controller(cmot)

        # one click on the video = pause / play, double click = fullscreen
        vclick = Gtk.GestureClick()
        vclick.set_propagation_phase(Gtk.PropagationPhase.CAPTURE)
        vclick.connect("pressed", self._video_pressed)
        self.video.add_controller(vclick)

        self.title = Gtk.Label(xalign=0, wrap=True, selectable=True)
        self.title.add_css_class("title-2")
        self.meta = Gtk.Label(xalign=0)
        self.meta.add_css_class("tube-meta")
        self.msg = Gtk.Label(xalign=0, wrap=True)
        self.msg.add_css_class("tube-meta")

        # channel row: avatar + name ... subscribe / unsubscribe, open in browser
        row = Gtk.Box(spacing=10)
        self.chan_av, self.chan_pic = avatar_widget(40)
        self.chan_av.set_valign(Gtk.Align.CENTER)
        g = Gtk.GestureClick()
        g.connect("released", self.open_channel)
        self.chan_av.add_controller(g)
        self.chan_av.set_cursor(Gdk.Cursor.new_from_name("pointer"))
        self.chan_btn = Gtk.Button(label="")
        self.chan_btn.add_css_class("flat")
        self.chan_btn.add_css_class("tube-title")
        self.chan_btn.connect("clicked", self.open_channel)
        self.sub_btn = Gtk.Button(label="Subscribe", valign=Gtk.Align.CENTER)
        style_sub(self.sub_btn, False)
        self.sub_btn.connect("clicked", self.toggle_sub)
        br = Gtk.Button(label="Open in browser", valign=Gtk.Align.CENTER)
        br.connect("clicked", lambda *_: Gio.AppInfo.launch_default_for_uri(
            self.url(), None))
        for b_ in (self.chan_av, self.chan_btn, self.sub_btn,
                   Gtk.Box(hexpand=True), br):
            row.append(b_)

        self.fix_btn = Gtk.Button(label="Update playback tools & retry",
                                  visible=False, halign=Gtk.Align.START)
        self.fix_btn.connect("clicked", lambda *_: app.install_tools_ui(
            lambda: self.play_stream("Retrying…")))
        self.desc = Gtk.Label(xalign=0, yalign=0, wrap=True, selectable=True,
                              wrap_mode=Pango.WrapMode.WORD_CHAR)
        self.comments = CommentsSection()
        for w in (self.player, self.title,
                  self.meta, row, self.msg,
                  self.fix_btn, self.desc, self.comments):
            left.append(w)
        self._pw = 0
        self._quality_values = ["screen"]
        self._stream_formats = {}
        self._stream_url = None
        self._quality_model_update = False
        self._stream_request = 0
        self._stream_retry_count = 0
        self._bad_codecs = set()  # codecs excluded entirely (this session)
        self._bad_streams = set()  # (codec, height) pairs that failed (this video)
        self._bad_containers = set()  # (codec, height, container) that failed
        self._notice = ""  # explanation shown next to "Streaming fixed ..."
        self._current_container = None
        self._http_403_retry_id = None
        self._http_403_retry_count = 0
        self._http_403_stream_tokens = set()
        self._pending_start_time = 0.0
        self._duration = 0
        self._position_base = 0.0  # where the current stream starts, in seconds
        self._want_playing = True
        self._selected_height = None
        self._timeline_updating = False
        self._timeline_dragging = False
        self._timeline_seek_source = 0
        self._seek_target = None  # pending arrow-key seek (applied after a pause)
        self._seek_commit_source = 0
        self._progress_source = 0
        self._t_start = 0.0
        self._stall_ts, self._stall_at = None, 0.0
        self._ts_origin, self._t_prepared = None, 0.0
        self.stream_server = FixedStreamServer(self._stream_failed)
        threading.Thread(target=self.stream_server.serve_forever,
                         daemon=True).start()
        self.right, self.row = right, row
        br.add_css_class("tube-sbtn")
        # Shorts: previous / next buttons (Up / Down keys work too)
        self.short_nav = Gtk.Box(spacing=10, halign=Gtk.Align.CENTER,
                                 visible=False)
        for text, d in (("▲ Previous", -1), ("Next ▼", 1)):
            nb = Gtk.Button(label=text)
            nb.add_css_class("tube-sbtn")
            nb.connect("clicked", lambda _b, d=d: app.short_step(d))
            self.short_nav.append(nb)
        left.append(self.short_nav)
        self.player.add_tick_callback(self._size_player)
        self.related = ItemGrid(app.open_item, mode="list", fixed_w=RELATED_W,
                                max_w=RELATED_W)
        for m in ("start", "end", "top"):
            getattr(self.related, f"set_margin_{m}")(0)
        rel_lbl = Gtk.Label(label="Related", xalign=0)
        rel_lbl.add_css_class("title-4")
        right.append(rel_lbl)
        right.append(self.related)

    # --- helpers
    @staticmethod
    def _hide_video_native_controls(video):
        children = [video.get_first_child()]
        while children:
            child = children.pop()
            while child:
                if isinstance(child, Gtk.MediaControls):
                    child.set_visible(False)
                    child.set_can_target(False)
                else:
                    nested = child.get_first_child()
                    if nested:
                        children.append(nested)
                child = child.get_next_sibling()

    @staticmethod
    def _video_center_play_indicator(video):
        children = [video.get_first_child()]
        while children:
            child = children.pop()
            while child:
                if (isinstance(child, Gtk.Image) and
                        child.get_icon_name() == "media-playback-start-symbolic" and
                        "osd" in child.get_css_classes()):
                    return child
                else:
                    nested = child.get_first_child()
                    if nested:
                        children.append(nested)
                child = child.get_next_sibling()
        return None

    def _set_video_center_play_indicator_visible(self, visible):
        indicator = self._video_center_play_indicator(self.video)
        if indicator:
            indicator.set_visible(visible)

    def _sync_video_center_play_indicator(self):
        stream = self.video.get_media_stream()
        visible = not self.loading_overlay.get_visible()
        if stream and stream.get_playing():
            visible = False
        self._set_video_center_play_indicator_visible(visible)

    def _video_playing_changed(self, *_):
        self._sync_video_center_play_indicator()

    def _video_media_stream_changed(self, *_):
        self._hide_video_native_controls(self.video)
        stream = self.video.get_media_stream()
        if stream:
            stream.connect("notify::playing", self._video_playing_changed)
            if self._want_playing or not stream.is_prepared():
                # An unprepared stream must preroll before a pause can apply.
                stream.set_playing(True)
        self._sync_video_center_play_indicator()

    def url(self):
        return f"https://www.youtube.com/watch?v={self.item['id']}"

    def set_desc(self, text):
        self.desc.set_markup(linkify((text or "")[:4000]))

    def show_status(self, text, spin=True):
        self.status.set_text(text)
        self.spinner.set_visible(spin)
        self.spinner.set_spinning(spin)
        if spin and self.mode == "stream":
            self.controls_row.set_visible(True)
        self.loading_overlay.set_visible(True)
        self._set_video_center_play_indicator_visible(False)
        self.player.set_visible_child_name("video")

    # --- click on the video: pause / play (double click = fullscreen)
    def _video_pressed(self, _g, n, _x, _y):
        if self._click_src:
            GLib.source_remove(self._click_src)
            self._click_src = 0
        if n == 1:  # wait briefly so a double click doesn't also pause
            self._click_src = GLib.timeout_add(250, self._single_click)
        elif n == 2:
            self.app.toggle_video_fullscreen()

    def _single_click(self):
        self._click_src = 0
        if self.mode == "stream":
            self._toggle_playback()
        return False

    # --- controls bar: auto-hide, volume
    def _on_motion(self, _c, x, y):
        if (x, y) == self._last_xy:  # GTK also reports synthetic moves
            return
        self._last_xy = (x, y)
        self._show_controls()

    def _show_controls(self):
        self.controls_row.set_opacity(1)
        self.controls_row.set_can_target(True)
        self.player.set_cursor(None)
        if self._ctl_src:
            GLib.source_remove(self._ctl_src)
        self._ctl_src = GLib.timeout_add(3000, self._maybe_hide_controls)

    def _maybe_hide_controls(self):
        self._ctl_src = 0
        stream = self.video.get_media_stream()
        if (self.mode == "stream" and not self._over_ctl and stream
                and stream.get_playing()):
            self.controls_row.set_opacity(0)
            self.controls_row.set_can_target(False)
            self.player.set_cursor(Gdk.Cursor.new_from_name("none"))
        return False

    def _apply_audio(self, stream=None):
        """Push volume / mute to the player and sync the volume widgets."""
        stream = stream or self.video.get_media_stream()
        v = int(self.app.settings.get("volume", 100))
        if stream and stream.is_prepared():
            stream.set_volume(v / 100)
            stream.set_muted(self._muted)
        self._vol_updating = True
        self.vol_scale.set_value(0 if self._muted else v)
        self._vol_updating = False
        self.vol_btn.set_icon_name(
            "audio-volume-muted-symbolic" if self._muted or v == 0 else
            "audio-volume-low-symbolic" if v < 34 else
            "audio-volume-medium-symbolic" if v < 67 else
            "audio-volume-high-symbolic")

    def _volume_scale_changed(self, scale):
        if self._vol_updating:
            return
        v = int(scale.get_value())
        self._muted = v == 0
        if v > 0:
            self.save_volume(v)
        self._apply_audio()

    def _toggle_mute(self, *_):
        if self._muted and int(self.app.settings.get("volume", 100)) == 0:
            self.save_volume(50)
        self._muted = not self._muted
        self._apply_audio()
        self._show_controls()

    # --- progress / seeking
    def _stream_prepared(self, stream, _pspec=None):
        if (stream is not self.video.get_media_stream() or
                not stream.is_prepared()):
            return
        self._http_403_retry_count = 0  # playback really started: fresh budget
        actual_start = (self.stream_server.get_start_time(self._stream_url)
                        if self._stream_url else None)
        if actual_start is not None:
            self._position_base = actual_start
        self._ts_origin, self._t_prepared = None, time.monotonic()
        self._stall_ts, self._stall_at = None, time.monotonic()
        self._apply_audio(stream)
        if self._want_playing and not stream.get_playing():
            stream.set_playing(True)
        elif not self._want_playing and stream.get_playing():
            stream.set_playing(False)
        self.player.set_visible_child_name("video")
        self.loading_overlay.set_visible(False)
        self.spinner.stop()
        self.controls_row.set_visible(self._duration > 0)
        self._sync_video_center_play_indicator()
        self._update_play_button(stream)
        self._show_controls()
        dlog(f"player ready {time.monotonic() - self._t_start:.1f}s after "
             "the stream was requested")
        if not self._progress_source:
            self._progress_source = GLib.timeout_add(
                250, self._update_progress)

    @staticmethod
    def _format_time(seconds):
        seconds = max(0, int(seconds))
        hours, rem = divmod(seconds, 3600)
        minutes, seconds = divmod(rem, 60)
        return (f"{hours}:{minutes:02}:{seconds:02}" if hours
                else f"{minutes}:{seconds:02}")

    def _current_position(self):
        """Stream start + what GTK's player reports (so stalls are counted)."""
        pos = self._position_base
        stream = self.video.get_media_stream()
        if self.mode == "stream" and stream and stream.is_prepared():
            ts = stream.get_timestamp() / 1e6
            if self._ts_origin is None and ts > 0 and stream.get_playing():
                # does GTK count from 0, or from the TS start offset (~0.5s)?
                guess = ts - (time.monotonic() - self._t_prepared)
                self._ts_origin = guess if guess > 0.25 else 0.0
            pos += max(0.0, ts - (self._ts_origin or 0.0))
        return min(pos, self._duration) if self._duration else pos

    def _update_progress(self):
        if self.mode != "stream":
            self._progress_source = 0
            return False
        position = self._current_position()
        if (not self._timeline_seek_source and not self._timeline_dragging
                and self._seek_target is None and self._duration):
            self._timeline_updating = True
            self.timeline.set_range(0, self._duration)
            self.timeline.set_value(position)
            self._timeline_updating = False
        if self._seek_target is None and not self._timeline_seek_source:
            self.current_time.set_text(self._format_time(position))

        stream = self.video.get_media_stream()
        if (stream and stream.is_prepared() and stream.get_playing()
                and not stream.get_ended() and self._want_playing
                and not self._timeline_seek_source
                and (not self._duration or position < self._duration - 2)):
            ts, now = stream.get_timestamp(), time.monotonic()
            # 1440p / 4K decode and buffer more slowly: allow a longer stall
            stall_limit = 15 if (self._selected_height or 0) > 1080 else 10
            if ts != self._stall_ts:
                self._stall_ts, self._stall_at = ts, now
            elif now - self._stall_at > stall_limit:
                self._stall_at = now
                dlog("playback stalled")
                if self._retry_stream("Playback stalled."):
                    return False

        self._update_play_button()
        return True

    def _update_play_button(self, stream=None):
        stream = stream or self.video.get_media_stream()
        playing = bool(stream and stream.get_playing())
        self.play_btn.set_icon_name(
            "media-playback-pause-symbolic" if playing
            else "media-playback-start-symbolic")
        self.play_btn.set_tooltip_text("Pause" if playing else "Play")

    def _toggle_playback(self, *_):
        stream = self.video.get_media_stream()
        if not stream or not stream.is_prepared():
            return
        playing = not stream.get_playing()
        stream.set_playing(playing)
        self._want_playing = playing
        self._update_play_button(stream)
        self._show_controls()  # stays visible while paused

    def _timeline_change_value(self, _scale, _scroll, value):
        """User clicked / dragged / used keys on the seek bar."""
        if not self._duration:
            return True
        value = max(0.0, min(float(value), float(self._duration)))
        self.current_time.set_text(self._format_time(value))
        if self._timeline_seek_source:
            GLib.source_remove(self._timeline_seek_source)
        # debounce: while dragging, only the final position is requested
        self._timeline_seek_source = GLib.timeout_add(
            400, self._commit_timeline_seek, value)
        self._show_controls()
        return False  # let GTK move the slider itself

    def _commit_timeline_seek(self, value):
        self._timeline_seek_source = 0
        self._seek_stream(value)
        return False

    def _seek_stream(self, position):
        if self.mode != "stream" or not self._stream_formats:
            return
        self._stream_retry_count = 0  # a user action earns a fresh retry
        current_position = self._current_position()
        target = max(0.0, min(float(position), self._duration))
        direction = ((target > current_position) -
                     (target < current_position))
        self._position_base = target
        self._start_selected_stream(
            self._selected_height, target, direction, current_position)

    def screen_video_height(self):
        display = self.get_display()
        native = self.get_native()
        surface = native.get_surface() if native else None
        monitor = display.get_monitor_at_surface(surface) if surface else None
        if monitor is None:
            monitors = display.get_monitors()
            monitor = monitors.get_item(0) if monitors.get_n_items() else None
        if monitor is None:
            return max(1, self.player.get_height() * self.get_scale_factor())
        return max(1, monitor.get_geometry().height * self.get_scale_factor())

    def _quality_changed(self, dropdown, _pspec):
        if self._quality_model_update or not self._stream_formats:
            return
        index = dropdown.get_selected()
        if index >= len(self._quality_values):
            return
        value = self._quality_values[index]
        current_position = self._current_position()
        self.app.settings["video_quality"] = value
        jsave(SETTINGS_FILE, self.app.settings)
        if self.mode == "stream":
            self._stream_retry_count = 0
            # the user picked a quality on purpose: forget earlier failures so
            # that this resolution is really attempted again
            self._bad_streams.clear()
            self._bad_containers.clear()
            self._notice = ""
            self._play_selected_stream(current_position)

    @staticmethod
    def _quality_label(height, fps, dynamic_range="SDR"):
        fps = int(fps or 0)
        hdr = (" HDR" if str(dynamic_range or "SDR").upper() != "SDR" else "")
        return f"{height}p{fps if fps > 30 else ''}{hdr}"

    def _set_quality_options(self, formats):
        heights = sorted(formats)
        desired = self.app.settings.get("video_quality", "screen")
        target = (screen_fit_height(heights, self.screen_video_height())
                  if desired == "screen"
                  else int(desired) if isinstance(desired, int) else
                  self.screen_video_height())
        selected_height = (target if desired == "screen"
                           else nearest_fixed_height(heights, target))
        sel_video = formats[nearest_fixed_height(heights, selected_height)]["video"]
        selected_label = self._quality_label(
            selected_height, sel_video.get("fps"), sel_video.get("dynamic_range"))
        labels = [f"Screen fit ({selected_label})"] + [
            self._quality_label(height, formats[height]["video"].get("fps"),
                                formats[height]["video"].get("dynamic_range"))
            for height in heights]
        self._quality_values = ["screen"] + heights
        if isinstance(desired, int) and desired not in formats:
            labels.insert(1, f"{desired}p (closest available: {selected_height}p)")
            self._quality_values.insert(1, desired)
        self._quality_model_update = True
        self.quality.set_model(Gtk.StringList.new(labels))
        if isinstance(desired, int) and desired in heights:
            self.quality.set_selected(self._quality_values.index(desired))
        elif isinstance(desired, int):
            self.quality.set_selected(1)
        else:
            self.quality.set_selected(0)
        self._quality_model_update = False
        self.quality.set_visible(bool(heights))
        return selected_height

    def _play_selected_stream(self, start_time=0):
        desired = self.app.settings.get("video_quality", "screen")
        target = (screen_fit_height(
                      self._stream_formats, self.screen_video_height())
                  if desired == "screen"
                  else int(desired) if isinstance(desired, int) else
                  self.screen_video_height())
        height = (target if desired == "screen"
                  else nearest_fixed_height(self._stream_formats, target))
        # `target` can be a height with no stream (e.g. a 1440p screen with only
        # 1080p / 2160p offered): always resolve it to one that exists.
        height = nearest_fixed_height(list(self._stream_formats), height)
        self._selected_height = height
        self._start_selected_stream(height, start_time)

    def _start_selected_stream(self, height, start_time, seek_direction=0,
                               seek_origin=None):
        spec = dict(self._stream_formats[height])
        spec["container"] = self._pick_container(spec, height)
        self._current_container = spec["container"]
        source = spec["video"]
        dlog(f"selected {height}p {source.get('vcodec')} "
             f"{source.get('fps')}fps {source.get('tbr')}kbps "
             f"({spec['container']}) client={source.get('__yt_dlp_client')} "
             f"range={source.get('dynamic_range')}")
        if self._stream_url:
            self.video.set_file(None)
            self._http_403_stream_tokens.discard(
                self._stream_url.rsplit("/", 1)[-1])
            self.stream_server.remove(self._stream_url)
        self._t_start = time.monotonic()
        self._ts_origin = None
        self._position_base = max(0, float(start_time))
        self._timeline_updating = True
        self.timeline.set_range(0, max(1, self._duration))
        self.timeline.set_value(self._position_base)
        self._timeline_updating = False
        self._stream_url = self.stream_server.add(
            spec, self._position_base, seek_direction, seek_origin,
            video_id=(self.item or {}).get("id"))
        qlabel = self._quality_label(height, source.get("fps"),
                                     source.get("dynamic_range"))
        note = f"  {self._notice}" if self._notice else ""
        dlog("stream url:", self._stream_url)
        self.msg.set_text(
            f"Streaming fixed {qlabel} "
            f"({str(spec.get('codec') or '?').upper()}).{note}")
        self.show_status(
            f"Connecting to fixed {qlabel} stream at "
            f"{self._format_time(self._position_base)}…")
        self.video.set_file(Gio.File.new_for_uri(self._stream_url))
        # 1440p / 4K need more time to probe, download and preroll
        GLib.timeout_add_seconds(
            30 if height > 1080 else 15,
            self._stream_prepare_timeout, self._stream_url)
        stream = self.video.get_media_stream()
        if stream:
            stream.connect("notify::error", self.on_play_error)
            if stream.is_prepared():
                self._stream_prepared(stream)
            else:
                stream.connect("notify::prepared", self._stream_prepared)
        else:
            self.player.set_visible_child_name("video")

    def _pick_container(self, spec, height=None):
        """First container for this codec (at this height) that hasn't failed."""
        codec = spec.get("codec")
        for container in CONTAINER_ORDER.get(codec, [spec["container"]]):
            if (codec, height, container) not in self._bad_containers:
                return container
        return spec["container"]

    def _stream_prepare_timeout(self, url):
        if self.mode != "stream" or self._stream_url != url:
            return False
        stream = self.video.get_media_stream()
        if stream and stream.is_prepared():
            return False
        error = stream.get_error() if stream else None
        reason = (error.message if error else
                  "GTK's media backend did not finish preparing the stream.")
        dlog(f"stream preparation timed out: prepared={bool(stream and stream.is_prepared())}, "
             f"playing={bool(stream and stream.get_playing())}, "
             f"timestamp={stream.get_timestamp() if stream else None}, error={reason}")
        if self._reload_after_http_403(reason):
            return False
        if self._retry_stream(f"The stream did not start ({reason})."):
            return False
        self._fail_stream(
            url, f"Fixed-quality stream failed to prepare: {reason}")
        return False

    def _fail_stream(self, url, message):
        if self.mode != "stream" or self._stream_url != url:
            return False
        self.show_status(message, False)
        self.video.set_file(None)
        self._http_403_stream_tokens.discard(url.rsplit("/", 1)[-1])
        self.stream_server.remove(url)
        self._stream_url = None
        self._position_base = 0
        self.timeline.set_sensitive(False)
        self.controls_row.set_visible(False)
        return False

    def _fall_back_codec(self, why):
        """If the current stream uses VP9 / AV1, try another container, then
        the other codec at the SAME height, and only then a lower height.

        Only the failing (codec, height) pair is excluded: a broken 4K VP9
        stream no longer disables 1080p VP9, or 4K AV1. True if a restart
        began. Network / 403 problems never reach here."""
        height = self._selected_height
        spec = self._stream_formats.get(height) or {}
        codec = spec.get("codec")
        if not codec or codec == "h264" or not self.item:
            return False
        self._bad_containers.add((codec, height, self._current_container))
        if any((codec, height, c) not in self._bad_containers
               for c in CONTAINER_ORDER.get(codec, [])):
            dlog(f"{codec} {height}p in {self._current_container} failed "
                 f"({why}); trying another container")
            self.play_stream(
                f"{why}\nTrying another stream container…",
                start_time=self._current_position())
            return True
        self._bad_streams.add((codec, height))
        self._notice = (f"{height}p {codec.upper()} would not play "
                        f"({str(why).strip().splitlines()[0][:80]}).")
        dlog(f"{codec} {height}p failed ({why}); excluding that stream only")
        self.play_stream(
            f"{why}\n{height}p {codec.upper()} doesn't play on this "
            "system, trying another stream…",
            start_time=self._current_position())
        return True

    def _retry_stream(self, why):
        """Resolve fresh stream URLs and restart once; True if a retry began.
        A failing VP9 / AV1 stream first falls back to another stream."""
        if self._fall_back_codec(why):
            return True
        if self._stream_retry_count >= 1 or not self.item:
            return False
        self._stream_retry_count += 1
        attempt = self._stream_retry_count
        position = self._current_position()
        _INFO_CACHE.pop(self.item["id"], None)
        dlog(f"automatic retry {attempt} of 1:", why)
        self.play_stream(
            f"{why}\nAutomatic retry {attempt} of 1 — "
            "refreshing stream URLs…",
            start_time=position, fresh=True)
        return True

    def _stream_failed(self, token, detail):
        current_token = (self._stream_url or "").rsplit("/", 1)[-1]
        if (self.mode == "stream" and token == current_token
                and re.search(r"\b403\b", str(detail))):
            self._http_403_stream_tokens.add(token)
        GLib.idle_add(self._show_stream_error, token, detail)

    def _show_stream_error(self, token, detail):
        if (not self._stream_url or
                self._stream_url.rsplit("/", 1)[-1] != token or
                self.mode != "stream"):
            return False
        if self._reload_after_http_403(detail):
            return False
        if self._retry_stream(str(detail).strip().splitlines()[-1][:120]
                              if str(detail).strip() else "Stream error."):
            return False
        return self._fail_stream(
            self._stream_url, f"Fixed-quality stream failed: {detail}")

    def _reload_after_http_403(self, detail):
        if not re.search(r"\b403\b", str(detail)):
            return False
        video_id = (self.item or {}).get("id")
        if not video_id:
            return False
        if self._http_403_retry_id != video_id:
            self._http_403_retry_id = video_id
            self._http_403_retry_count = 0
        self._http_403_retry_count += 1
        attempt = self._http_403_retry_count
        if self._http_403_retry_count > 2:
            message = f"YouTube denied the video stream (HTTP 403): {detail}"
            if self._stream_url:
                self._fail_stream(self._stream_url, message)
            else:
                self.show_status(message, False)
            return True
        # The cached URLs are the ones that just got denied: always re-resolve.
        _INFO_CACHE.pop(video_id, None)
        dlog(f"automatic HTTP 403 retry {attempt} of 2", video_id,
             "with fresh URLs")
        self.play_stream(
            f"YouTube denied the stream (HTTP 403).\n"
            f"Automatic retry {attempt} of 2 — fetching fresh stream URLs…",
            start_time=self._current_position(), fresh=True)
        return True

    def stop(self):
        self.app.set_video_fullscreen(False)
        self._stop_playback()

    def _stop_playback(self):
        self.mode = None
        self._stream_request += 1
        self._stream_formats = {}
        self._selected_height = None
        self._duration = 0
        self._position_base = 0
        self._want_playing = True
        self._seek_target = None
        self._timeline_updating = True
        self._timeline_dragging = False
        self.timeline.set_range(0, 1)
        self.timeline.set_value(0)
        self._timeline_updating = False
        self.timeline.set_sensitive(False)
        self.controls_row.set_visible(False)
        self.controls_row.set_opacity(1)
        self.controls_row.set_can_target(True)
        self.player.set_cursor(None)
        self.current_time.set_text("0:00")
        self.duration_label.set_text("0:00")
        self.play_btn.set_icon_name("media-playback-pause-symbolic")
        for attr in ("_progress_source", "_timeline_seek_source",
                     "_seek_commit_source", "_ctl_src", "_click_src"):
            src = getattr(self, attr)
            if src:
                GLib.source_remove(src)
                setattr(self, attr, 0)
        self.quality.set_visible(False)
        if self.web is not None:
            self.web.load_uri("about:blank")  # silences audio
        self.video.set_file(None)
        if self._stream_url:
            self._http_403_stream_tokens.discard(
                self._stream_url.rsplit("/", 1)[-1])
            self.stream_server.remove(self._stream_url)
            self._stream_url = None

    def _size_player(self, *_):
        """Keep the player 16:9 for full-size video streams."""
        if self._fs:
            return GLib.SOURCE_CONTINUE
        if self.short:  # tall 9:16 player that fills the window height
            h = self.get_height()
            if h and h != self._ph:
                self._ph = h
                ph = max(360, h - 190)
                self.player.set_size_request(ph * 9 // 16, ph)
            return GLib.SOURCE_CONTINUE
        w = self.player.get_width()
        if w and w != self._pw:
            self._pw = w
            self.player.set_size_request(-1, min(w * 9 // 16, 720))
        return GLib.SOURCE_CONTINUE

    def set_fullscreen(self, on):
        """Hide everything but the player so it fills the whole window."""
        if on == self._fs:
            return
        self._fs = on
        if on:
            self._fix_was = self.fix_btn.get_visible()
            self.fix_btn.set_visible(False)
        elif self._fix_was:
            self.fix_btn.set_visible(True)
        self._apply_layout()
        for side, v in (("top", 12), ("bottom", 12), ("start", 16), ("end", 16)):
            getattr(self.outer, f"set_margin_{side}")(0 if on else v)
        self.outer.set_spacing(0 if on else 16)
        self.left.set_spacing(0 if on else 8)
        for w in (self.outer, self.left, self.player):
            w.set_vexpand(on)
        self._apply_policy()
        self.player.set_size_request(-1, -1)
        if on:
            self.player.remove_css_class("tube-player")
        else:
            self.player.add_css_class("tube-player")
        self._pw = self._ph = 0
        self._apply_shape()
        self.get_vadjustment().set_value(0)
        self.fs_btn.set_icon_name("view-restore-symbolic" if on
                                  else "view-fullscreen-symbolic")

    # --- Shorts mode: vertical player on black, no sidebar / description
    def set_short_mode(self, on):
        if on == self.short:
            return
        self.short = on
        al = Gtk.Align.CENTER if on else Gtk.Align.FILL
        for w in (self.title, self.row, self.msg):
            w.set_halign(al)
        self.title.set_justify(Gtk.Justification.CENTER if on
                               else Gtk.Justification.LEFT)
        self.title.set_max_width_chars(40 if on else -1)
        if on:
            self.add_css_class("tube-shorts-bg")
        else:
            self.remove_css_class("tube-shorts-bg")
            self.player.set_size_request(-1, 480)
        self._pw = self._ph = 0
        self._apply_layout()
        self._apply_policy()
        self._apply_shape()

    def _apply_layout(self):
        fs, sh = self._fs, self.short
        for w in (self.meta, self.desc, self.comments, self.right):
            w.set_visible(not fs and not sh)
        for w in (self.title, self.row, self.msg):
            w.set_visible(not fs)
        self.short_nav.set_visible(sh and not fs)

    def _apply_policy(self):
        self.set_policy(Gtk.PolicyType.EXTERNAL,
                        Gtk.PolicyType.NEVER if (self._fs or self.short)
                        else Gtk.PolicyType.AUTOMATIC)

    def _apply_shape(self):
        if self._fs:
            al, ex = Gtk.Align.FILL, True
        elif self.short:
            al, ex = Gtk.Align.CENTER, False
        else:
            al, ex = Gtk.Align.FILL, True
        self.player.set_halign(al)
        self.player.set_hexpand(ex)

    def js(self, code):
        if self.web is None:
            return
        try:
            self.web.evaluate_javascript(code, -1, None, None, None, None)
        except TypeError:
            self.web.evaluate_javascript(code, -1, None, None, None, None, None)

    def ensure_web(self):
        if self.web is None:
            WK, session = webkit_env()
            if not WK:
                return None
            try:  # allow autoplay (with sound) without a user gesture
                pol = WK.WebsitePolicies(autoplay=WK.AutoplayPolicy.ALLOW)
                self.web = WK.WebView(network_session=session,
                                      website_policies=pol)
            except Exception:  # noqa: BLE001
                self.web = WK.WebView(network_session=session)
            s = self.web.get_settings()
            s.set_media_playback_requires_user_gesture(False)  # autoplay
            try:
                s.set_media_playback_allows_inline(True)
            except Exception:  # noqa: BLE001
                pass
            s.set_user_agent(DESKTOP_UA)  # desktop player layout
            ucm = self.web.get_user_content_manager()
            ucm.register_script_message_handler("ytevent", None)
            for code in (NOTOUCH_JS, CONSENT_JS, EMBED_JS):
                ucm.add_script(WK.UserScript.new(
                    code, WK.UserContentInjectedFrames.ALL_FRAMES,
                    WK.UserScriptInjectionTime.START, None, None))
            ucm.connect("script-message-received::ytevent", self.on_yt_msg)
            self.web.connect("context-menu", lambda *_: True)
            # take over fullscreen so the video covers the whole window
            # the player's own button / key asks for fullscreen: toggle it
            self.web.connect("enter-fullscreen", lambda *_: (
                self.app.toggle_video_fullscreen(), True)[1])
            self.web.connect("leave-fullscreen", lambda *_: (
                self.app.set_video_fullscreen(False), True)[1])
            self.player.add_named(self.web, "web")
        return self.web

    # --- opening / playing
    def open(self, item):
        if (self.item and self.item.get("id") != item.get("id")):
            self._http_403_retry_id = None
            self._http_403_retry_count = 0
        self.item = item
        self._stream_retry_count = 0
        self._pending_start_time = 0
        # per-video: which (codec, height) streams failed, and why
        self._bad_streams = set()
        self._bad_containers = set()
        self._notice = ""
        self.set_short_mode(item.get("kind") == "short")
        self.info = {}
        self.gen += 1
        gen = self.gen
        self.stop()
        self.comments.clear()
        self.fix_btn.set_visible(False)
        self.title.set_text(item.get("title", ""))
        self.meta.set_text("")
        self.desc.set_text("")
        self.msg.set_text("")
        self.chan_btn.set_label(item.get("channel", ""))
        self.chan_pic.set_paintable(None)
        self.update_sub_btn()
        self.update_avatar()
        self.show_status("Loading video…")

        def fn():  # title / channel / description / related, in a single call
            d = watch_details(item["id"])
            GLib.idle_add(self.apply_details, gen, d)
            return d["related"]
        self.related.load(fn)
        self.play_stream()

    def apply_details(self, gen, d):
        if gen != self.gen:
            return False
        self.info.update({k: v for k, v in d.items() if k != "related" and v})
        if d.get("title"):
            self.title.set_text(d["title"])
        if d.get("channel"):
            self.chan_btn.set_label(d["channel"])
        self.meta.set_text(" · ".join(x for x in (d.get("views"), d.get("date")) if x))
        self.set_desc(d.get("desc"))
        self.update_sub_btn()
        self.update_avatar()
        self.comments.start(d.get("comment_token"))
        return False

    def update_avatar(self):
        cid = self.cid()
        if not cid:
            return
        if AVATARS.get(cid):
            load_thumb(AVATARS[cid], self.chan_pic)
            return
        gen = self.gen

        def done(_r, _e):
            if gen == self.gen and AVATARS.get(cid):
                load_thumb(AVATARS[cid], self.chan_pic)
        run_async(lambda: ensure_avatars([cid]), done)

    def play_embedded(self, *_):
        web = self.ensure_web()
        if web is None:
            if self.short:
                self.show_status(
                    "Shorts playback needs the in-app web player. "
                    "Install gir1.2-webkit-6.0.", False)
            else:
                self.play_stream(
                    "The in-app web player needs gir1.2-webkit-6.0.")
            return
        gen = self.gen
        self.mode = "embed"
        self.show_status("Loading video…")
        vid = self.item["id"]
        loop = f',loop:1,playlist:"{vid}"' if self.short else ""  # shorts loop
        web.load_html(EMBED_HTML.replace("__ID__", vid)
                      .replace("__LOOP__", loop)
                      .replace("__ORIGIN__", EMBED_ORIGIN), EMBED_ORIGIN + "/")
        GLib.timeout_add_seconds(20, self._embed_timeout, gen)

    def _embed_timeout(self, gen):
        if gen == self.gen and self.mode == "embed":
            if self.short:
                self.mode = None
                self.show_status("The Shorts player did not respond.", False)
            else:
                self.play_stream("The embedded player did not respond.")
        return False

    def on_yt_msg(self, _ucm, value):
        try:
            m = value.to_string()
        except Exception:  # noqa: BLE001
            return
        if self.mode not in ("embed", "web"):
            return
        if m == "fs":  # double click on the video
            self.app.toggle_video_fullscreen()
            return
        if m.startswith("cc:"):  # user turned subtitles on / off
            self.save_captions(m[3:] == "1")
            return
        if m.startswith("vol:"):  # volume changed with the player's own slider
            try:
                self.save_volume(int(m[4:]))
            except ValueError:
                pass
            return
        if m == "ready":
            if self.mode == "embed":
                self.mode = "web"
                self.msg.set_text("")
                self.player.set_visible_child_name("web")
                self.loading_overlay.set_visible(False)
                self.spinner.stop()
                v = self.app.settings.get("volume")  # remembered volume
                self.js('gtkMsg({gtk:"vol",v:%s})' % ("null" if v is None
                                                      else int(v)))
                # remembered subtitle choice (default: off)
                self.js('gtkMsg({gtk:"cfg",cc:%s})' % (
                    "true" if self.app.settings.get("captions", False)
                    else "false"))
        elif m.startswith("error:"):
            if m == "error:100":
                self.mode = None
                self.show_status("This video is unavailable.", False)
            else:
                code = m[6:]
                why = {"2": "invalid parameter", "5": "HTML5 player error",
                       "101": "embedding disabled by the owner",
                       "150": "embedding disabled by the owner",
                       "153": "missing referrer / player configuration"
                       }.get(code, "unknown")
                detail = f"Embedded player error {code} ({why})."
                if self.short:
                    self.mode = None
                    self.show_status(detail, False)
                else:
                    self.play_stream(detail)

    # --- volume (one value, shared by every video, remembered)
    def save_volume(self, v):
        self.app.settings["volume"] = max(0, min(100, int(v)))
        if not self._vsave:
            self._vsave = GLib.timeout_add(600, self._flush_settings)

    def save_captions(self, on):
        self.app.settings["captions"] = bool(on)
        if not self._vsave:
            self._vsave = GLib.timeout_add(600, self._flush_settings)

    def _flush_settings(self):
        self._vsave = 0
        jsave(SETTINGS_FILE, self.app.settings)
        return False

    def _throttle(self, key, gap):
        """True if `key` fired less than `gap` seconds ago (key auto-repeat)."""
        now = time.monotonic()
        last = self.__dict__.setdefault("_thr", {})
        if now - last.get(key, 0) < gap:
            return True
        last[key] = now
        return False

    def adjust_volume(self, delta):
        """Up / Down keys: change the volume by `delta` percent."""
        if self._throttle("vol", 0.1):
            return
        v = max(0, min(100, int(self.app.settings.get("volume", 100)) + delta))
        self.save_volume(v)
        self.player.show_osd(f"Volume {v}%", v / 100)
        if self.mode == "web":
            self.js('gtkMsg({gtk:"vol",v:%d,show:true})' % v)
        elif self.mode == "stream":
            self._muted = False
            self._apply_audio()

    def seek_by(self, secs):
        """Arrow keys: jump `secs` seconds. Repeated presses add up and the
        stream is restarted only once, shortly after the last press."""
        if self.mode == "web":
            if self._throttle("seek", 0.15):
                return
            now = time.monotonic()
            if now - self.__dict__.get("_sk_t", 0) > 1.5:
                self._sk_acc = 0
            self._sk_t = now
            self._sk_acc = self.__dict__.get("_sk_acc", 0) + secs
            a = self._sk_acc
            self.player.show_osd(
                f"◀◀ {-a}s" if a < 0 else f"{a}s ▶▶" if a > 0 else "0s")
            self.js('gtkMsg({gtk:"seek",d:%d})' % secs)
        elif self.mode == "stream" and self._duration:
            if self._throttle("seek", 0.1):
                return
            base = (self._seek_target if self._seek_target is not None
                    else self._current_position())
            target = max(0.0, min(base + secs, max(0.0, self._duration - 1)))
            self._seek_target = target
            self.player.show_osd(
                f"{self._format_time(target)} / {self._format_time(self._duration)}",
                target / self._duration)
            self.current_time.set_text(self._format_time(target))
            self._timeline_updating = True
            self.timeline.set_value(target)
            self._timeline_updating = False
            if self._seek_commit_source:
                GLib.source_remove(self._seek_commit_source)
            self._seek_commit_source = GLib.timeout_add(
                450, self._commit_seek_target)
            self._show_controls()

    def _commit_seek_target(self):
        self._seek_commit_source = 0
        target, self._seek_target = self._seek_target, None
        if target is not None:
            self._seek_stream(target)
        return False

    def play_stream(self, why="", start_time=0, fresh=False):
        """Resolve a fixed-quality stream with yt-dlp (cached) and play it."""
        if not self.item:
            return
        if not os.path.exists(YTDLP):
            self.stop()
            self.show_status(f"{why}\nInstall the playback tools (banner at the "
                             "top) to play videos.", False)
            self.fix_btn.set_visible(True)
            return
        self._stop_playback()
        self.mode = "stream"
        self._pending_start_time = max(0, float(start_time))
        self._t_start = time.monotonic()
        self.show_status(why + ("\n" if why else "") +
                         "Finding fixed-quality streams…")
        self.msg.set_text(why)
        gen = self.gen
        request = self._stream_request
        run_async(lambda: ytdlp_info(self.url(), fresh=fresh),
                  lambda i, e: self.stream_ready(gen, request, i, e))

    def stream_ready(self, gen, request, info, err):
        if (gen != self.gen or request != self._stream_request or
                self.mode != "stream"):
            return
        if err or not info:
            if self._reload_after_http_403(err or ""):
                return
            if self._retry_stream(f"Could not load the stream: {err}"):
                return
            self.show_status(f"Could not load the stream: {err}", False)
            self.fix_btn.set_visible(True)
            return
        if not self.desc.get_text():
            self.set_desc(info.get("description"))
        self._duration = max(0, float(info.get("duration") or 0))
        self.duration_label.set_text(self._format_time(self._duration))
        self.timeline.set_sensitive(self._duration > 0)
        try:
            decoders = available_gstreamer_codecs()
        except (ImportError, ValueError) as exc:
            self.show_status(
                f"Could not inspect GStreamer decoders: {exc}", False)
            return
        dlog("GStreamer decoders:", sorted(decoders))
        dlog("yt-dlp video formats:", describe_formats(info))
        dlog("excluded codecs:", sorted(self._bad_codecs),
             "excluded streams:", sorted(self._bad_streams))
        formats = fixed_stream_formats(
            info, decoders, self._bad_codecs, self._bad_streams,
            self.app.settings.get("video_codec_preference",
                                  DEFAULT_CODEC_PREFERENCE))
        if not formats:
            self.show_status(
                "No H.264, VP9, or AV1 stream is compatible with the "
                "installed GStreamer decoders for this video. Install the "
                "matching codecs and restart the app.", False)
            return
        if not shutil.which("ffmpeg"):
            self.show_status(
                "FFmpeg is required to stream fixed-quality video with audio. "
                "Install it with: sudo apt install ffmpeg", False)
            return
        # 1440p / 4K only come as VP9 / AV1: say so if no decoder exists
        no_dec = [c.upper() for c in ("vp9", "av1") if c not in decoders]
        if no_dec and max(formats) <= 1080 and not self._notice:
            self._notice = (
                f"No {' / '.join(no_dec)} decoder is installed, so 1440p / 4K "
                "are unavailable (sudo apt install gstreamer1.0-plugins-good "
                "gstreamer1.0-libav).")
        elif max(formats) <= 1080 and not self._notice:
            self._notice = ("YouTube returned no plain 1440p / 4K stream for "
                            "this video (run with GTKTUBE_DEBUG=1 to see the "
                            "formats).")
        self._stream_formats = formats
        self._set_quality_options(formats)
        self._play_selected_stream(self._pending_start_time)

    def on_play_error(self, stream, _p):
        if stream is not self.video.get_media_stream():
            return
        token = (self._stream_url or "").rsplit("/", 1)[-1]
        if token in self._http_403_stream_tokens:
            self._reload_after_http_403("HTTP 403 from YouTube media server")
            return
        e = stream.get_error()
        detail = f"In-app playback failed ({e.message if e else '?'})."
        if self._reload_after_http_403(e.message if e else ""):
            return
        if self._retry_stream(detail):
            return
        self._fail_stream(self._stream_url, detail)

    # --- channel / subscribe
    def cid(self):
        return self.info.get("channel_id") or (self.item or {}).get("channel_id")

    def update_sub_btn(self):
        style_sub(self.sub_btn, self.cid() in self.app.subs.d)

    def toggle_sub(self, *_):
        if self.cid():
            now = self.app.subs.toggle(self.cid(), self.chan_btn.get_label())
            self.app.push_sub(self.cid(), now)
            self.update_sub_btn()

    def open_channel(self, *_):
        if self.cid():
            self.app.go("channel", self.cid())


class ChannelPage(Gtk.Box):
    """Channel page: banner, then avatar + name + handle / subscribers / video
    count + Subscribe, then the channel's videos."""

    def __init__(self, app):
        super().__init__(orientation=Gtk.Orientation.VERTICAL)
        self.app, self.cid, self.name, self._bw = app, None, "", 0
        content = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)

        # banner (hidden when the channel has none)
        self.banner = Gtk.Picture(content_fit=Gtk.ContentFit.COVER,
                                  can_shrink=True, hexpand=True, margin_top=12,
                                  margin_start=16, margin_end=16, visible=False)
        self.banner.add_css_class("tube-chan-banner")
        self.banner.set_overflow(Gtk.Overflow.HIDDEN)
        self.banner.add_tick_callback(self._size_banner)

        # avatar | name + "@handle · subscribers · videos" + about | subscribe
        info = Gtk.Box(spacing=16, margin_top=14, margin_bottom=4,
                       margin_start=16, margin_end=16)
        self.av, self.av_pic = avatar_widget(88)
        self.av.set_valign(Gtk.Align.CENTER)
        col = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=3,
                      valign=Gtk.Align.CENTER, hexpand=True)
        self.title = Gtk.Label(xalign=0, wrap=True)
        self.title.add_css_class("title-1")
        self.meta = Gtk.Label(xalign=0, wrap=True)
        self.meta.add_css_class("tube-meta")
        self.about = Gtk.Label(xalign=0, wrap=True, lines=2, max_width_chars=90,
                               ellipsize=Pango.EllipsizeMode.END, visible=False)
        self.about.add_css_class("tube-meta")
        for w in (self.title, self.meta, self.about):
            col.append(w)
        self.sub = Gtk.Button(label="Subscribe", valign=Gtk.Align.CENTER)
        style_sub(self.sub, False)
        self.sub.connect("clicked", self.toggle)
        for w in (self.av, col, self.sub):
            info.append(w)

        self.grid = ItemGrid(app.open_item)
        for w in (self.banner, info, self.grid):
            content.append(w)
        self.append(scrolled(content))

    def _size_banner(self, w, _clock):
        width = w.get_width()
        if width and width != self._bw:
            self._bw = width
            w.set_size_request(-1, max(90, min(width // 6, 280)))
        return GLib.SOURCE_CONTINUE

    def open(self, cid):
        self.cid, self.name = cid, ""
        self.title.set_text("Loading…")
        self.meta.set_text("")
        self.about.set_visible(False)
        self.banner.set_paintable(None)
        self.banner.set_visible(False)
        self.av_pic.set_paintable(None)
        if AVATARS.get(cid):
            load_thumb(AVATARS[cid], self.av_pic)
        self.refresh_btn()

        def fn():
            hdr = {}
            name, items = channel_fetch(cid, ("videos",), hdr)
            self.name = name
            GLib.idle_add(self._apply_header, cid, hdr)
            return items
        self.grid.load(fn)

    def _apply_header(self, cid, h):
        if cid != self.cid:
            return False
        if h.get("name"):
            self.name = h["name"]
        self.title.set_text(self.name or cid)
        self.meta.set_text(" · ".join(
            x for x in (h.get("handle"), h.get("subs"), h.get("videos")) if x))
        desc = (h.get("desc") or "").strip().replace("\n", " ")
        self.about.set_text(desc)
        self.about.set_visible(bool(desc))
        if h.get("avatar"):
            load_thumb(h["avatar"], self.av_pic)
        if h.get("banner"):
            self.banner.set_visible(True)
            load_thumb(h["banner"], self.banner,
                       lambda: self.banner.set_visible(False))
        return False

    def refresh_btn(self):
        style_sub(self.sub, self.cid in self.app.subs.d)

    def toggle(self, *_):
        now = self.app.subs.toggle(self.cid, self.name or self.cid)
        self.app.push_sub(self.cid, now)
        self.refresh_btn()


class SearchPage(Gtk.Box):
    FILTERS = {0: None, 1: "EgIQAQ==", 2: "EgIQAg=="}

    def __init__(self, app):
        super().__init__(orientation=Gtk.Orientation.VERTICAL)
        self.q, self.filter = "", 0
        bar = Gtk.Box(spacing=12, margin_top=10, margin_bottom=4,
                      margin_start=16, margin_end=16)
        self.heading = Gtk.Label(xalign=0, hexpand=True)
        self.heading.add_css_class("title-3")
        chips = Gtk.Box()
        chips.add_css_class("linked")
        first = None
        for i, name in enumerate(("All", "Videos", "Channels")):
            b = Gtk.ToggleButton(label=name, active=(i == 0))
            if first:
                b.set_group(first)
            else:
                first = b
            b.connect("toggled", self.on_chip, i)
            chips.append(b)
        bar.append(self.heading)
        bar.append(chips)
        self.grid = ItemGrid(app.open_item, mode="list", max_w=1000)
        self.append(bar)
        self.append(scrolled(self.grid))

    def on_chip(self, b, i):
        if b.get_active() and i != self.filter:
            self.filter = i
            if self.q:
                self.run(self.q)

    def run(self, q):
        self.q = q
        self.heading.set_text(f"Results for “{q}”")
        body = {"query": q}
        if self.FILTERS[self.filter]:
            body["params"] = self.FILTERS[self.filter]
        self.grid.load(lambda: parse_items(innertube("search", **body)),
                       f"No results for “{q}”.")


# --------------------------------------------------------------------- app


class Window(Gtk.ApplicationWindow):
    NAV = [("home", "Home", "go-home-symbolic"),
           ("shorts", "Shorts", "camera-video-symbolic"),
           ("posts", "Posts", "user-available-symbolic"),
           ("subs", "Subscriptions", "starred-symbolic")]
    BROWSERS = ["firefox", "chrome", "chromium", "brave", "vivaldi", "edge"]

    def __init__(self, app):
        settings = jload(SETTINGS_FILE, {})
        saved_geometry = settings.get("window_geometry", {})
        if not isinstance(saved_geometry, dict):
            saved_geometry = {}

        def saved_dimension(name, default):
            value = saved_geometry.get(name)
            return (value if isinstance(value, int) and not isinstance(value, bool)
                    and 200 <= value <= 10000 else default)

        width = saved_dimension("width", 1400)
        height = saved_dimension("height", 900)
        super().__init__(application=app, title="YouTube",
                         default_width=width, default_height=height)
        self.subs = Subs()
        self.settings = settings
        self._normal_window_size = (width, height)
        self._saved_window_geometry = saved_geometry
        self._last_window_geometry = None
        self._geometry_save_source = 0
        self._position_restore_attempts = 0
        self.history, self.current = [], None
        self._vfs = False
        self.short_q, self._more_busy = [], False  # Shorts queue

        hb = self.hb = Gtk.HeaderBar()
        self.set_titlebar(hb)
        brand = Gtk.Box(spacing=6, valign=Gtk.Align.CENTER)
        brand_icon = Gtk.Image(icon_name="media-playback-start-symbolic")
        brand_icon.add_css_class("accent")
        brand_name = Gtk.Label(label="YouTube")
        brand_name.add_css_class("title-4")
        brand.append(brand_icon)
        brand.append(brand_name)
        hb.pack_start(brand)
        self.back = Gtk.Button(icon_name="go-previous-symbolic", visible=False)
        self.back.connect("clicked", self.go_back)
        hb.pack_start(self.back)
        mouse_back = Gtk.GestureClick()
        mouse_back.set_button(0)
        mouse_back.set_propagation_phase(Gtk.PropagationPhase.CAPTURE)
        mouse_back.connect("pressed", self._mouse_back_pressed)
        self.add_controller(mouse_back)
        hb.pack_end(self.build_account_menu())
        settings_btn = Gtk.Button(icon_name="preferences-system-symbolic")
        settings_btn.set_tooltip_text("Settings")
        settings_btn.connect("clicked", self.open_settings)
        hb.pack_end(settings_btn)
        refresh = Gtk.Button(icon_name="view-refresh-symbolic")
        refresh.connect("clicked", lambda *_: self.reload())
        hb.pack_end(refresh)
        self.location_stack = Gtk.Stack(
            transition_type=Gtk.StackTransitionType.NONE)
        self.location_stack.set_hexpand(False)
        self.location_button = Gtk.Button()
        self.location_button.set_hexpand(True)
        self.location_button.add_css_class("flat")
        self.location_content = Gtk.Box(spacing=6, hexpand=True)
        self.location_icon = Gtk.Image(
            icon_name="media-playback-start-symbolic", visible=False)
        self.location_label = Gtk.Label(
            xalign=0, hexpand=True, ellipsize=Pango.EllipsizeMode.MIDDLE)
        self.location_content.append(self.location_icon)
        self.location_content.append(self.location_label)
        self.location_button.set_child(self.location_content)
        self.location_button.connect("clicked", self._edit_location)
        self.location_stack.add_named(self.location_button, "display")
        self.entry = Gtk.SearchEntry(
            placeholder_text="Search or paste link",
            width_chars=55)
        self.entry.add_css_class("tube-search-entry")
        self.entry.connect("activate", self._activate_location)
        self.entry.connect("search-changed", self._schedule_search_suggestions)
        self.location_stack.add_named(self.entry, "edit")
        self.location_stack.set_visible_child_name("display")
        hb.set_title_widget(self.location_stack)
        self.suggest_popover = Gtk.Popover()
        self.suggest_popover.set_has_arrow(False)
        self.suggest_popover.set_autohide(True)
        self.suggest_list = Gtk.ListBox(
            selection_mode=Gtk.SelectionMode.SINGLE,
            activate_on_single_click=True)
        self.suggest_list.connect("row-activated",
                                  self._search_suggestion_activated)
        suggest_scroll = Gtk.ScrolledWindow(
            hscrollbar_policy=Gtk.PolicyType.NEVER,
            vscrollbar_policy=Gtk.PolicyType.AUTOMATIC,
            max_content_height=360, propagate_natural_height=True)
        suggest_scroll.set_child(self.suggest_list)
        suggest_scroll.set_size_request(420, -1)
        self.suggest_popover.set_child(suggest_scroll)
        self.suggest_popover.set_parent(self.entry)
        self._suggestion_generation = 0
        self._suggestion_timeout = 0
        kc = Gtk.EventControllerKey()
        kc.set_propagation_phase(Gtk.PropagationPhase.CAPTURE)
        kc.connect("key-pressed", self.on_key)
        self.add_controller(kc)
        entry_keys = Gtk.EventControllerKey()
        entry_keys.set_propagation_phase(Gtk.PropagationPhase.CAPTURE)
        entry_keys.connect("key-pressed", self._location_key_pressed)
        self.entry.add_controller(entry_keys)
        entry_focus = Gtk.EventControllerFocus()
        entry_focus.connect("leave", self._location_focus_left)
        entry_focus.connect("enter", self._schedule_search_suggestions)
        self.entry.add_controller(entry_focus)
        self._add_location_click_away(hb)

        page = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        self._add_location_click_away(page)
        self.set_child(page)
        # banner for installing/updating yt-dlp + deno
        self.banner = Gtk.Revealer(reveal_child=False)
        bbox = Gtk.Box(spacing=12)
        bbox.add_css_class("tube-banner")
        self.banner_lbl = Gtk.Label(xalign=0, hexpand=True, wrap=True)
        self.banner_btn = Gtk.Button(label="Install")
        self.banner_btn.connect("clicked", lambda *_: self.install_tools_ui())
        bbox.append(self.banner_lbl)
        bbox.append(self.banner_btn)
        self.banner.set_child(bbox)
        page.append(self.banner)
        # banner shown when GStreamer lacks codecs the player needs
        self.codec_banner = Gtk.Revealer(reveal_child=False)
        cbox = Gtk.Box(spacing=12)
        cbox.add_css_class("tube-banner")
        self.codec_lbl = Gtk.Label(xalign=0, hexpand=True, wrap=True,
                                   selectable=True)
        self.codec_cmd = ""
        b_copy = Gtk.Button(label="Copy command")
        b_copy.connect("clicked", lambda *_: self.get_clipboard().set(self.codec_cmd))
        b_hide = Gtk.Button(label="Dismiss")
        b_hide.connect("clicked", lambda *_: self.codec_banner.set_reveal_child(False))
        for w in (self.codec_lbl, b_copy, b_hide):
            cbox.append(w)
        self.codec_banner.set_child(cbox)
        page.append(self.codec_banner)

        root = Gtk.Box(vexpand=True)
        page.append(root)
        self.sidebar = Gtk.ListBox(selection_mode=Gtk.SelectionMode.SINGLE)
        self.sidebar.add_css_class("navigation-sidebar")
        self.sidebar.set_size_request(180, -1)
        for key, text, icon in self.NAV:
            row = Gtk.ListBoxRow()
            row.key = key
            b = Gtk.Box(spacing=10, margin_top=8, margin_bottom=8,
                        margin_start=10, margin_end=10)
            b.append(Gtk.Image(icon_name=icon))
            b.append(Gtk.Label(label=text, xalign=0))
            row.set_child(b)
            self.sidebar.append(row)
        self.sidebar.connect("row-activated",
                             lambda _l, r: self.go(r.key, clear=True))
        self.sidebar.select_row(self.sidebar.get_row_at_index(0))
        root.append(self.sidebar)
        self.side_sep = Gtk.Separator(orientation=Gtk.Orientation.VERTICAL)
        root.append(self.side_sep)

        self.stack = Gtk.Stack(hexpand=True, vexpand=True)
        root.append(self.stack)
        o = self.open_item
        self.grids = {
            "home": ItemGrid(o, target=4, min_w=250),
            "shorts": ItemGrid(o, target=7, min_w=150),
            "posts": ItemGrid(o, target=1, min_w=420, max_w=720),
            "subs": ItemGrid(o, target=4, min_w=250),
        }
        for k, g in self.grids.items():
            self.stack.add_named(scrolled(g), k)
        self.search_page = SearchPage(self)
        self.grids["search"] = self.search_page.grid
        self.stack.add_named(self.search_page, "search")
        self.watch = WatchPage(self)
        self.channel = ChannelPage(self)
        self.stack.add_named(self.watch, "watch")
        self.stack.add_named(self.channel, "channel")
        self.connect("close-request", self._close_playback)
        self._window_geometry_source = GLib.timeout_add_seconds(
            1, self._poll_window_geometry)

        self.refresh_account()
        if logged_in():
            self.merge_account_subs()
            self.fetch_account()
        self.check_tools()
        self.check_codecs()
        self.go("home", clear=True)

    def restore_window_state(self):
        geometry = self._saved_window_geometry
        if geometry.get("maximized"):
            self.maximize()
        if (not geometry.get("maximized")
                and geometry.get("position_backend") == "x11"
                and isinstance(geometry.get("x"), int)
                and isinstance(geometry.get("y"), int)):
            self._position_restore_attempts = 30
            GLib.timeout_add(100, self._restore_x11_position)

    def _restore_x11_position(self):
        if GdkX11 is None or not isinstance(
                self.get_display(), GdkX11.X11Display):
            return GLib.SOURCE_REMOVE
        surface = self.get_surface()
        if not isinstance(surface, GdkX11.X11Surface):
            self._position_restore_attempts -= 1
            if self._position_restore_attempts > 0:
                return GLib.SOURCE_CONTINUE
            return GLib.SOURCE_REMOVE
        _x11_move_window(
            self, self._saved_window_geometry["x"],
            self._saved_window_geometry["y"])
        return GLib.SOURCE_REMOVE

    def _poll_window_geometry(self):
        width, height = self.get_width(), self.get_height()
        if width <= 0 or height <= 0:
            return GLib.SOURCE_CONTINUE
        maximized = self.is_maximized()
        fullscreen = self.is_fullscreen()
        position = None if maximized or fullscreen else _x11_window_position(self)
        snapshot = (width, height, maximized, fullscreen, position)
        if snapshot != self._last_window_geometry:
            self._last_window_geometry = snapshot
            if self._geometry_save_source:
                GLib.source_remove(self._geometry_save_source)
            self._geometry_save_source = GLib.timeout_add(
                500, self._save_window_geometry)
        return GLib.SOURCE_CONTINUE

    def _save_window_geometry(self):
        self._geometry_save_source = 0
        geometry = dict(self._saved_window_geometry)
        maximized = self.is_maximized()
        fullscreen = self.is_fullscreen()
        if not maximized and not fullscreen:
            width, height = self.get_width(), self.get_height()
            if width > 0 and height > 0:
                self._normal_window_size = (width, height)
            geometry["width"], geometry["height"] = self._normal_window_size
            position = _x11_window_position(self)
            if position is not None:
                geometry["x"], geometry["y"] = position
                geometry["position_backend"] = "x11"
        if not fullscreen:
            geometry["maximized"] = maximized
        self._saved_window_geometry = geometry
        self.settings["window_geometry"] = geometry
        jsave(SETTINGS_FILE, self.settings)
        return GLib.SOURCE_REMOVE

    def _close_playback(self, *_):
        if self._window_geometry_source:
            GLib.source_remove(self._window_geometry_source)
            self._window_geometry_source = 0
        if self._geometry_save_source:
            GLib.source_remove(self._geometry_save_source)
            self._geometry_save_source = 0
        self._save_window_geometry()
        self.watch.stop()
        threading.Thread(
            target=self.watch.stream_server.close, daemon=True).start()
        return False

    def _mouse_back_pressed(self, gesture, _presses, _x, _y):
        if gesture.get_current_button() == 8 and self.history:
            gesture.set_state(Gtk.EventSequenceState.CLAIMED)
            self.go_back()

    def _location_url(self):
        name, arg = self.current or ("home", None)
        if name == "watch" and isinstance(arg, dict) and arg.get("id"):
            return f"https://www.youtube.com/watch?v={arg['id']}"
        if name == "channel" and arg:
            return f"https://www.youtube.com/channel/{arg}"
        return "https://www.youtube.com/"

    def _update_location(self):
        name, arg = self.current or ("home", None)
        if name in ("watch", "channel"):
            url = self._location_url()
            self.location_icon.set_visible(name == "watch")
            self.location_label.set_text(
                "YouTube Video" if name == "watch" else "YouTube Channel")
            self.location_button.set_tooltip_text(url)
            self.entry.set_text(url)
            self.location_stack.set_visible_child_name("display")
        else:
            self.location_icon.set_visible(False)
            self.entry.set_text(arg if name == "search" and arg else "")
            self.location_button.set_tooltip_text("")
            self.location_stack.set_visible_child_name("edit")
        self.entry.set_tooltip_text("")
        self.entry.remove_css_class("error")

    def _edit_location(self, *_):
        self.entry.set_text(self._location_url())
        self.location_stack.set_visible_child_name("edit")
        self.entry.grab_focus()
        self.entry.select_region(0, -1)

    def _collapse_location(self):
        name = self.current[0] if self.current else "home"
        if (name in ("watch", "channel")
                and self.location_stack.get_visible_child_name() == "edit"):
            self._update_location()
        return False

    def _schedule_search_suggestions(self, *_):
        if self._suggestion_timeout:
            GLib.source_remove(self._suggestion_timeout)
            self._suggestion_timeout = 0
        if not self.entry.has_focus() and not self.suggest_popover.get_visible():
            return
        self._suggestion_generation += 1
        generation = self._suggestion_generation
        query = self.entry.get_text().strip()
        if not query:
            self._show_search_history(generation)
        self._suggestion_timeout = GLib.timeout_add(
            250, self._fetch_search_suggestions, generation, query)

    def _search_history(self):
        history = self.settings.get("search_history", [])
        if not isinstance(history, list):
            return []
        return [query for query in history
                if isinstance(query, str) and query.strip()]

    def _dismissed_search_history(self):
        dismissed = self.settings.get("dismissed_search_history", [])
        if not isinstance(dismissed, list):
            return []
        return [query for query in dismissed
                if isinstance(query, str) and query.strip()]

    def _append_search_history_row(self, query):
        row = Gtk.ListBoxRow(activatable=False, selectable=False)
        content = Gtk.Box(
            spacing=6, margin_top=4, margin_bottom=4,
            margin_start=6, margin_end=6)
        search_button = Gtk.Button(halign=Gtk.Align.FILL, hexpand=True)
        search_button.add_css_class("flat")
        search_content = Gtk.Box(spacing=10)
        search_content.append(Gtk.Image(
            icon_name="document-open-recent-symbolic"))
        search_content.append(Gtk.Label(
            label=query, xalign=0, hexpand=True))
        search_button.set_child(search_content)
        search_button.connect(
            "clicked", self._search_history_activated, query)
        clear_button = Gtk.Button(
            icon_name="window-close-symbolic", valign=Gtk.Align.CENTER)
        clear_button.add_css_class("flat")
        clear_button.set_tooltip_text("Remove this search from suggestions")
        clear_button.connect(
            "clicked", self._clear_search_history_entry, query)
        content.append(search_button)
        content.append(clear_button)
        row.set_child(content)
        self.suggest_list.append(row)

    def _show_search_history(self, generation):
        if (generation != self._suggestion_generation
                or self.entry.get_text().strip()
                or (not self.entry.has_focus()
                    and not self.suggest_popover.get_visible())
                or self.location_stack.get_visible_child_name() != "edit"):
            return
        while (row := self.suggest_list.get_first_child()):
            self.suggest_list.remove(row)
        dismissed = {
            item.casefold() for item in self._dismissed_search_history()}
        for query in self._search_history():
            if query.casefold() not in dismissed:
                self._append_search_history_row(query)
        if self.suggest_list.get_first_child():
            self.suggest_popover.popup()
        else:
            self.suggest_popover.popdown()

    def _search_history_activated(self, _button, query):
        self.suggest_popover.popdown()
        self.entry.set_text(query)
        self._activate_location(self.entry)

    def _clear_search_history_entry(self, _button, query):
        self.settings["search_history"] = [
            item for item in self._search_history()
            if item.casefold() != query.casefold()]
        dismissed = [item for item in self._dismissed_search_history()
                     if item.casefold() != query.casefold()]
        self.settings["dismissed_search_history"] = [
            query, *dismissed][:SEARCH_HISTORY_LIMIT]
        jsave(SETTINGS_FILE, self.settings)
        self._schedule_search_suggestions()

    def _record_search_query(self, query):
        query = query.strip()
        if not query:
            return
        history = [item for item in self._search_history()
                   if item.casefold() != query.casefold()]
        self.settings["search_history"] = [query, *history][
            :SEARCH_HISTORY_LIMIT]
        self.settings["dismissed_search_history"] = [
            item for item in self._dismissed_search_history()
            if item.casefold() != query.casefold()]
        jsave(SETTINGS_FILE, self.settings)

    def _fetch_search_suggestions(self, generation, query):
        self._suggestion_timeout = 0
        run_async(
            lambda: youtube_search_suggestions(query),
            lambda result, error: self._show_search_suggestions(
                generation, query, result, error))
        return GLib.SOURCE_REMOVE

    def _show_search_suggestions(self, generation, query, suggestions, error):
        if (generation != self._suggestion_generation
                or query != self.entry.get_text().strip()
                or not self.entry.has_focus()
                or self.location_stack.get_visible_child_name() != "edit"):
            return
        while (row := self.suggest_list.get_first_child()):
            self.suggest_list.remove(row)
        seen = set()
        dismissed = {
            item.casefold() for item in self._dismissed_search_history()}
        if not query:
            for text in self._search_history():
                normalized = text.casefold()
                if normalized not in dismissed:
                    self._append_search_history_row(text)
                    seen.add(normalized)
        if error:
            row = Gtk.ListBoxRow(activatable=False, selectable=False)
            row.set_child(Gtk.Label(
                label=f"Could not load YouTube suggestions: {error}",
                xalign=0, wrap=True, margin_top=8, margin_bottom=8,
                margin_start=12, margin_end=12))
            self.suggest_list.append(row)
        else:
            for text, is_history in suggestions:
                normalized = text.casefold()
                if normalized in seen or (
                        is_history and normalized in dismissed):
                    continue
                if is_history:
                    self._append_search_history_row(text)
                    seen.add(normalized)
                    continue
                row = Gtk.ListBoxRow()
                content = Gtk.Box(
                    spacing=10, margin_top=6, margin_bottom=6,
                    margin_start=12, margin_end=12)
                icon = "document-open-recent-symbolic" if is_history \
                    else "system-search-symbolic"
                content.append(Gtk.Image(icon_name=icon))
                content.append(Gtk.Label(label=text, xalign=0, hexpand=True))
                row.query_text = text
                row.set_child(content)
                self.suggest_list.append(row)
        if self.suggest_list.get_first_child():
            self.suggest_popover.popup()
        else:
            self.suggest_popover.popdown()

    def _search_suggestion_activated(self, _list, row):
        query = row.query_text
        self.suggest_popover.popdown()
        self.entry.set_text(query)
        self._activate_location(self.entry)

    def _add_location_click_away(self, widget):
        gesture = Gtk.GestureClick()
        gesture.set_propagation_phase(Gtk.PropagationPhase.CAPTURE)
        gesture.connect("pressed", self._location_click_away, widget)
        widget.add_controller(gesture)

    def _location_click_away(self, _gesture, _presses, x, y, widget):
        if (self.location_stack.get_visible_child_name() != "edit"
                or not self.current or self.current[0] not in ("watch", "channel")):
            return
        target = widget.pick(x, y, Gtk.PickFlags.DEFAULT)
        while target:
            if target is self.entry:
                return
            target = target.get_parent()
        GLib.idle_add(self._collapse_location)

    def _location_focus_left(self, *_):
        if self.suggest_popover.get_visible():
            return
        GLib.idle_add(self._collapse_location)

    def _location_key_pressed(self, _controller, keyval, _keycode, _state):
        if keyval == Gdk.KEY_Escape:
            self.suggest_popover.popdown()
            self._collapse_location()
            return True
        if (keyval in (Gdk.KEY_Up, Gdk.KEY_Down)
                and self.suggest_popover.get_visible()):
            row = self.suggest_list.get_selected_row()
            if row is None:
                row = (self.suggest_list.get_last_child()
                       if keyval == Gdk.KEY_Up
                       else self.suggest_list.get_first_child())
            elif keyval == Gdk.KEY_Up:
                row = row.get_prev_sibling() or row
            else:
                row = row.get_next_sibling() or row
            if row and hasattr(row, "query_text"):
                self.suggest_list.select_row(row)
                return True
        if (keyval in (Gdk.KEY_Return, Gdk.KEY_KP_Enter)
                and self.suggest_popover.get_visible()):
            row = self.suggest_list.get_selected_row()
            if row and hasattr(row, "query_text"):
                self._search_suggestion_activated(self.suggest_list, row)
                return True
        return False

    def _activate_location(self, entry):
        self._suggestion_generation += 1
        if self._suggestion_timeout:
            GLib.source_remove(self._suggestion_timeout)
            self._suggestion_timeout = 0
        self.suggest_popover.popdown()
        value = entry.get_text().strip()
        if not value:
            self._collapse_location()
            return
        video_id = youtube_video_id(value)
        if video_id:
            item = {"kind": "video", "id": video_id, "title": video_id,
                    "channel": "", "channel_id": ""}
            self.go("watch", item)
        elif is_youtube_url(value):
            entry.add_css_class("error")
            entry.set_tooltip_text(
                "Paste a YouTube watch, Shorts, live, embed, or youtu.be link.")
        else:
            self.go("search", value)
            self._record_search_query(value)

    def on_key(self, _c, keyval, _code, _state):
        w = self.watch
        on_watch = bool(self.current and self.current[0] == "watch")
        on_video = on_watch and w.mode in ("web", "stream")
        typing = isinstance(self.get_focus(), Gtk.Editable)
        mods = _state & (Gdk.ModifierType.CONTROL_MASK | Gdk.ModifierType.ALT_MASK
                         | Gdk.ModifierType.SUPER_MASK)
        if on_video and not mods:
            if keyval == Gdk.KEY_F11 or (keyval in (Gdk.KEY_f, Gdk.KEY_F)
                                         and not typing):
                self.toggle_video_fullscreen()
                return True
            if keyval in (Gdk.KEY_Up, Gdk.KEY_Down) and not typing:
                w.adjust_volume(5 if keyval == Gdk.KEY_Up else -5)
                return True
            if keyval in (Gdk.KEY_Left, Gdk.KEY_Right) and not typing:
                w.seek_by(5 if keyval == Gdk.KEY_Right else -5)
                return True
            if keyval == Gdk.KEY_space and not typing and w.mode == "stream":
                w._toggle_playback()
                return True
            if keyval in (Gdk.KEY_m, Gdk.KEY_M) and not typing and w.mode == "stream":
                w._toggle_mute()
                return True
        if (on_watch and w.short and not typing
                and keyval in (Gdk.KEY_Page_Down, Gdk.KEY_Page_Up)):
            self.short_step(1 if keyval == Gdk.KEY_Page_Down else -1)
            return True
        if keyval == Gdk.KEY_Escape and self._vfs:
            self.watch.js("document.exitFullscreen&&document.exitFullscreen()")
            self.set_video_fullscreen(False)
            return True
        return False

    def toggle_video_fullscreen(self):
        """F / F11 / double click / the player's button: toggle video fullscreen."""
        now = time.monotonic()
        if now - getattr(self, "_fs_t", 0) < 0.4:  # one action may fire twice
            return
        self._fs_t = now
        if self._vfs:
            self.watch.js("document.exitFullscreen&&document.exitFullscreen()")
            self.set_video_fullscreen(False)
        else:
            self.set_video_fullscreen(True)

    def set_video_fullscreen(self, on):
        """Video fullscreen: window fullscreen + hide every other UI element."""
        if on == self._vfs:
            return
        self._vfs = on
        for w in (self.hb, self.sidebar, self.side_sep, self.banner,
                  self.codec_banner):
            w.set_visible(not on)
        self.watch.set_fullscreen(on)
        if on:
            self.fullscreen()
        else:
            self.unfullscreen()
            self.watch.js('gtkMsg({gtk:"reveal"})')  # show controls + cursor again

    def check_codecs(self):
        def done(missing, _e):
            if not shutil.which("ffmpeg"):
                missing = [*missing, "FFmpeg"]
            if not missing:
                return
            try:
                with open("/etc/os-release") as f:
                    mint = "linuxmint" in f.read().lower()
            except OSError:
                mint = False
            pkg = "mint-meta-codecs" if mint else "ubuntu-restricted-extras"
            self.codec_cmd = (f"sudo apt install {pkg} ffmpeg gstreamer1.0-libav "
                              "gstreamer1.0-plugins-good gstreamer1.0-plugins-bad")
            self.codec_lbl.set_text(
                f"Missing video codecs ({', '.join(missing)}). Videos may not "
                f"play or may stutter. Install them, then restart the app:\n"
                f"{self.codec_cmd}")
            self.codec_banner.set_reveal_child(True)
        run_async(missing_codecs, done)

    # --- playback tools --------------------------------------------------
    def check_tools(self):
        if not tools_ready():
            self.banner_lbl.set_text("Install yt-dlp + deno for fixed-quality "
                                     "video playback and browser login import.")
            self.banner_btn.set_label("Install now")
            self.banner_btn.set_sensitive(True)
            self.banner.set_reveal_child(True)
            return
        run_async(tool_versions, lambda v, _e: self.tools_lbl.set_text(v or ""))
        # YouTube breaks yt-dlp often: refresh it in the background when stale
        if time.time() - os.path.getmtime(YTDLP) > 2 * 86400:
            run_async(lambda: install_tools(lambda s: None),
                      lambda v, e: self.tools_lbl.set_text(v or ""))

    def install_tools_ui(self, done_cb=None):
        self.banner_lbl.set_text("Downloading yt-dlp and deno…")
        self.banner_btn.set_sensitive(False)
        self.banner.set_reveal_child(True)

        def fn():
            return install_tools(
                lambda s: GLib.idle_add(self.banner_lbl.set_text, s))

        def done(v, err):
            if err:
                self.banner_lbl.set_text(f"Install failed: {err}")
                self.banner_btn.set_label("Retry")
                self.banner_btn.set_sensitive(True)
                return
            self.tools_lbl.set_text(v or "")
            self.banner.set_reveal_child(False)
            _INFO_CACHE.clear()  # URLs resolved by the old yt-dlp may be stale
            if done_cb:
                done_cb()
        run_async(fn, done)

    def open_settings(self, *_):
        if getattr(self, "settings_window", None):
            self.settings_window.present()
            return

        win = Gtk.Window(title="Settings", transient_for=self, modal=True,
                         default_width=460, default_height=400)
        self.settings_window = win
        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=14,
                      margin_top=20, margin_bottom=20,
                      margin_start=20, margin_end=20)
        heading = Gtk.Label(label="Video playback", xalign=0)
        heading.add_css_class("title-3")
        codec_row = Gtk.Box(spacing=12)
        codec_label = Gtk.Label(label="Preferred codec order", xalign=0,
                                hexpand=True)
        codec_dropdown = Gtk.DropDown.new_from_strings(
            [label for _value, label in CODEC_PREFERENCE_OPTIONS])
        codec_dropdown.set_tooltip_text(
            "Try codecs in this order at each resolution.")
        current_preference = self.settings.get(
            "video_codec_preference", DEFAULT_CODEC_PREFERENCE)
        option_values = [value for value, _label in CODEC_PREFERENCE_OPTIONS]
        if current_preference not in option_values:
            current_preference = DEFAULT_CODEC_PREFERENCE
        codec_dropdown.set_selected(option_values.index(current_preference))
        codec_dropdown.connect("notify::selected",
                               self._codec_preference_changed)
        codec_row.append(codec_label)
        codec_row.append(codec_dropdown)
        hardware_row = Gtk.Box(spacing=12)
        hardware_label = Gtk.Label(label="Hardware video decoding",
                                   xalign=0, hexpand=True)
        hardware_preference = self.settings.get(
            "hardware_video_decoding", HWDEC)
        if not isinstance(hardware_preference, bool):
            hardware_preference = HWDEC
        hardware_switch = Gtk.Switch(
            active=hardware_preference, valign=Gtk.Align.CENTER)
        hardware_switch.set_tooltip_text(
            "Use supported hardware video decoders instead of software decoding.")
        hardware_row.append(hardware_label)
        hardware_row.append(hardware_switch)
        hardware_detail = Gtk.Label(
            label="At next launch: " +
                  ("enabled" if hardware_preference else "disabled") +
                  ". Restart GtkTube after changing this setting. Hardware "
                  "decoding can improve performance, but may cause blank or "
                  "frozen video on some systems.",
            xalign=0, wrap=True)
        hardware_detail.add_css_class("tube-meta")
        hardware_switch.connect("notify::active",
                                self._hardware_decoding_changed,
                                hardware_detail)
        detail = Gtk.Label(
            label="1440p, 4K and HDR are offered whenever GStreamer can decode "
                  "VP9 / AV1, regardless of your monitor (HDR is shown "
                  "without tone mapping on an SDR screen). The preferred "
                  "codec is tried first at each resolution; if it is "
                  "unavailable or fails, the next codec is tried. Changing "
                  "the preference restarts current fixed-quality playback.",
            xalign=0, wrap=True)
        detail.add_css_class("tube-meta")
        close_btn = Gtk.Button(label="Close", halign=Gtk.Align.END)
        close_btn.connect("clicked", lambda *_: win.close())
        box.append(heading)
        box.append(codec_row)
        box.append(hardware_row)
        box.append(hardware_detail)
        box.append(detail)
        box.append(close_btn)
        win.set_child(box)
        win.connect("close-request", self._settings_closed)
        win.present()

    def _hardware_decoding_changed(self, switch, _pspec, detail):
        enabled = switch.get_active()
        self.settings["hardware_video_decoding"] = enabled
        jsave(SETTINGS_FILE, self.settings)
        detail.set_text(
            "At next launch: " + ("enabled" if enabled else "disabled") +
            ". Restart GtkTube after changing this setting. Hardware "
            "decoding can improve performance, but may cause blank or frozen "
            "video on some systems.")

    def _codec_preference_changed(self, dropdown, _pspec):
        index = dropdown.get_selected()
        if index >= len(CODEC_PREFERENCE_OPTIONS):
            return
        preference = CODEC_PREFERENCE_OPTIONS[index][0]
        if self.settings.get("video_codec_preference",
                             DEFAULT_CODEC_PREFERENCE) == preference:
            return
        self.settings["video_codec_preference"] = preference
        jsave(SETTINGS_FILE, self.settings)

        page = self.watch
        if page.mode != "stream" or not page.item:
            return
        start_time = page._current_position()
        want_playing = page._want_playing
        page._bad_streams.clear()
        page._bad_containers.clear()
        page.play_stream(
            f"Changing codec preference to {preference.upper()}…",
            start_time=start_time)
        page._want_playing = want_playing

    def _settings_closed(self, *_):
        self.settings_window = None
        return False

    # --- account ---------------------------------------------------------
    def build_account_menu(self):
        mb = Gtk.MenuButton(icon_name="avatar-default-symbolic")
        pop = Gtk.Popover()
        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=14,
                      margin_top=16, margin_bottom=16,
                      margin_start=16, margin_end=16)
        box.set_size_request(320, -1)

        self.acct_stack = Gtk.Stack(vhomogeneous=False,
                                    transition_type=Gtk.StackTransitionType.CROSSFADE)

        # --- signed in: avatar, name, log out
        si = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=14)
        who = Gtk.Box(spacing=12)
        self.acct_av, self.acct_pic = avatar_widget(56)
        self.acct_av.set_valign(Gtk.Align.CENTER)
        names = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2,
                        valign=Gtk.Align.CENTER, hexpand=True)
        self.acct_name = Gtk.Label(xalign=0, wrap=True, max_width_chars=22)
        self.acct_name.add_css_class("title-3")
        self.acct_handle = Gtk.Label(xalign=0, wrap=True, max_width_chars=26)
        self.acct_handle.add_css_class("tube-meta")
        names.append(self.acct_name)
        names.append(self.acct_handle)
        who.append(self.acct_av)
        who.append(names)
        b_out = Gtk.Button(label="Log out")
        b_out.add_css_class("destructive-action")
        b_out.connect("clicked", lambda *_: self.sign_out())
        si.append(who)
        si.append(b_out)

        # --- signed out: sign-in options
        so = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=12)
        head = Gtk.Label(label="Sign in", xalign=0)
        head.add_css_class("title-3")
        blurb = Gtk.Label(label="Sign in to see your subscriptions and "
                                "personalized recommendations.",
                          xalign=0, wrap=True, max_width_chars=34)
        blurb.add_css_class("tube-meta")
        b_google = Gtk.Button(label="Sign in with Google…")
        b_google.add_css_class("suggested-action")
        b_google.connect("clicked", lambda *_: self.login_webkit())
        exp = Gtk.Expander(label="Import login from a browser")
        ibox = Gtk.Box(spacing=6, margin_top=8)
        self.browser_dd = Gtk.DropDown.new_from_strings(self.BROWSERS)
        self.browser_dd.set_hexpand(True)
        b_imp = Gtk.Button(label="Import")
        b_imp.connect("clicked", lambda *_: self.import_browser())
        ibox.append(self.browser_dd)
        ibox.append(b_imp)
        exp.set_child(ibox)
        for w in (head, blurb, b_google, exp):
            so.append(w)

        self.acct_stack.add_named(si, "in")
        self.acct_stack.add_named(so, "out")
        box.append(self.acct_stack)

        self.acct_msg = Gtk.Label(xalign=0, wrap=True, max_width_chars=38,
                                  visible=False)
        self.acct_msg.add_css_class("tube-meta")
        box.append(self.acct_msg)

        # --- tools footer
        box.append(Gtk.Separator())
        trow = Gtk.Box(spacing=8)
        tcol = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2, hexpand=True)
        tt = Gtk.Label(label="Playback tools", xalign=0)
        self.tools_lbl = Gtk.Label(xalign=0, wrap=True, max_width_chars=28)
        self.tools_lbl.add_css_class("tube-meta")
        tcol.append(tt)
        tcol.append(self.tools_lbl)
        b_tools = Gtk.Button(label="Update", valign=Gtk.Align.CENTER)
        b_tools.connect("clicked", lambda *_: self.install_tools_ui())
        trow.append(tcol)
        trow.append(b_tools)
        box.append(trow)

        pop.set_child(box)
        mb.set_popover(pop)
        return mb

    def set_acct_msg(self, text):
        self.acct_msg.set_text(text)
        self.acct_msg.set_visible(bool(text))

    def refresh_account(self):
        ok = logged_in()
        self.acct_stack.set_visible_child_name("in" if ok else "out")
        if ok:
            acc = self.settings.get("account") or {}
            self.acct_name.set_text(acc.get("name") or "Signed in")
            self.acct_handle.set_text(acc.get("handle", ""))
            self.acct_handle.set_visible(bool(acc.get("handle")))
            load_thumb(acc.get("photo"), self.acct_pic)

    def fetch_account(self):
        def done(info, _err):
            if info and info.get("name"):
                self.settings["account"] = info
                jsave(SETTINGS_FILE, self.settings)
                self.refresh_account()
        run_async(account_info, done)

    def after_login(self):
        self.refresh_account()
        self.fetch_account()
        self.set_acct_msg("")
        self.merge_account_subs()
        for g in self.grids.values():
            g.loaded = False
        self.reload()

    def login_webkit(self):
        WK, session = webkit_env()
        if not WK:
            self.set_acct_msg("Install: sudo apt install gir1.2-webkit-6.0 "
                              "gir1.2-soup-3.0 - or use the browser import.")
            return
        view = WK.WebView(network_session=session)
        view.get_settings().set_user_agent(SAFARI_UA)
        win = Gtk.Window(title="Sign in to Google", default_width=520,
                         default_height=720, transient_for=self, child=view)
        state = {"busy": False}

        def finish(cookies):
            state["busy"] = False
            rows = []
            for c in cookies:
                exp = c.get_expires()
                rows.append((c.get_domain(), c.get_path(), c.get_secure(),
                             int(exp.to_unix()) if exp else 0, c.get_name(),
                             c.get_value(), c.get_http_only()))
            write_netscape(rows)
            if logged_in():
                win.close()
                self.after_login()

        def on_load(v, event):
            uri = v.get_uri() or ""
            if (event != WK.LoadEvent.FINISHED or state["busy"]
                    or not uri.startswith("https://www.youtube.com")):
                return
            state["busy"] = True
            got, pending = [], [2]

            def cb(mgr, res):
                try:
                    got.extend(mgr.get_cookies_finish(res))
                except GLib.Error:
                    pass
                pending[0] -= 1
                if pending[0] == 0:
                    finish(got)
            mgr = session.get_cookie_manager()
            mgr.get_cookies("https://www.youtube.com/", None, cb)
            mgr.get_cookies("https://accounts.google.com/", None, cb)

        view.connect("load-changed", on_load)
        view.load_uri("https://accounts.google.com/ServiceLogin?service=youtube"
                      "&continue=https%3A%2F%2Fwww.youtube.com%2F")
        win.present()

    def import_browser(self):
        browser = self.BROWSERS[self.browser_dd.get_selected()]
        if not os.path.exists(YTDLP):
            self.set_acct_msg("Install the playback tools first (banner at the top).")
            return
        self.set_acct_msg(f"Reading {browser} cookies…")

        def fn():
            tmp = os.path.join(CONF_DIR, "cookies.import.tmp")
            os.makedirs(CONF_DIR, exist_ok=True)
            p = subprocess.run(
                [sys.executable, YTDLP, "--no-warnings", "--cookies-from-browser",
                 browser, "--cookies", tmp, "--simulate", "--ignore-no-formats-error",
                 "--remote-components", "ejs:github",
                 "https://www.youtube.com/watch?v=jNQXAC9IVRk"],
                capture_output=True, text=True, timeout=180, env=tool_env())
            try:
                rows = parse_netscape(tmp)
            except OSError:
                rows = []
            finally:
                try:
                    os.remove(tmp)
                except OSError:
                    pass
            if not rows:
                lines = [l for l in p.stderr.splitlines() if l.strip()]
                raise RuntimeError(lines[-1][:200] if lines else "no cookies found")
            write_netscape(rows)  # keeps only google/youtube cookies
            return logged_in()

        def done(ok, err):
            if err:
                self.set_acct_msg(f"Import failed: {err}")
            elif ok:
                self.after_login()
            else:
                self.set_acct_msg(f"No YouTube login found in {browser}. "
                                  "Sign in there first.")
        run_async(fn, done)

    def sign_out(self):
        try:
            os.remove(COOKIES)
        except OSError:
            pass
        WK, session = webkit_env()
        if session:  # forget the Google login of the sign-in / player view
            try:
                session.get_website_data_manager().clear(
                    WK.WebsiteDataTypes.ALL, 0, None, None, None)
            except Exception:  # noqa: BLE001
                pass
        self.settings.pop("account", None)
        jsave(SETTINGS_FILE, self.settings)
        self.refresh_account()
        self.set_acct_msg("")
        for g in self.grids.values():
            g.loaded = False
        self.reload()

    def merge_account_subs(self):
        def fn():
            return [i for i in parse_items(
                innertube("browse", browseId="FEchannels"))
                if i["kind"] == "channel"]

        def done(items, _err):
            if items:
                for i in items:
                    self.subs.d.setdefault(i["id"], i["title"])
                    remember_avatar(i["id"], i.get("thumb"))
                self.subs.save()
        run_async(fn, done)

    def push_sub(self, cid, subscribe):
        """Best-effort sync of a local (un)subscribe to the Google account."""
        if not logged_in():
            return

        def fn():
            body = {"channelIds": [cid]}
            if subscribe:
                body["params"] = "EgIIAhgA"
            innertube("subscription/subscribe" if subscribe
                      else "subscription/unsubscribe", **body)

        def done(_r, err):
            if err:
                self.set_acct_msg(f"Account sync failed: {err}")
        run_async(fn, done)

    # --- navigation ------------------------------------------------------
    def go(self, name, arg=None, push=True, clear=False):
        if clear:
            self.history.clear()
        if push and self.current and not clear:
            self.history.append(self.current)
        if self.current and self.current[0] == "watch" and name != "watch":
            self.watch.stop()
        self.current = (name, arg)
        self.stack.set_visible_child_name(name)
        self.back.set_visible(bool(self.history))
        self._update_location()
        if name == "watch":
            self.watch.open(arg)
        elif name == "channel":
            self.channel.open(arg)
        elif name == "search":
            if arg:
                self.entry.set_text(arg)
                self.search_page.run(arg)
        elif not self.grids[name].loaded or not push:
            self.load_feed(name)

    def go_back(self, *_):
        if self.history:
            name, arg = self.history.pop()
            self.go(name, arg, push=False)
            self.back.set_visible(bool(self.history))

    def reload(self):
        name, arg = self.current
        if name in self.grids and name != "search":
            self.load_feed(name)
        elif name == "search" and arg:
            self.search_page.run(arg)
        elif name in ("watch", "channel"):
            if name == "watch":
                self.watch._http_403_retry_id = None
                self.watch._http_403_retry_count = 0
            self.go(name, arg, push=False)

    def short_step(self, d):
        """Go to the next / previous short of the queue (loads more at the end)."""
        ids = [s["id"] for s in self.short_q]
        cur = (self.watch.item or {}).get("id")
        j = (ids.index(cur) if cur in ids else -1) + d
        if j < 0:
            return
        if j < len(self.short_q):
            self.go("watch", self.short_q[j], push=False)
            return
        if self._more_busy:
            return
        self._more_busy = True

        def done(items, _e):
            self._more_busy = False
            seen = set(ids)
            self.short_q.extend(x for x in (items or []) if x["id"] not in seen)
            if j < len(self.short_q):
                self.go("watch", self.short_q[j], push=False)
        run_async(self.shorts_feed, done)

    def open_item(self, item):
        k = item["kind"]
        if k == "short":
            g = self.grids.get(self.current[0]) if self.current else None
            q = [i for i in (g.items if g else []) if i["kind"] == "short"]
            self.short_q = q if any(s["id"] == item["id"] for s in q) else [item]
            self.go("watch", item)
        elif k == "video":
            self.go("watch", item)
        elif k == "channel":
            self.go("channel", item["id"])
        elif k == "post":
            Gio.AppInfo.launch_default_for_uri(
                f"https://www.youtube.com/post/{item['id']}", None)

    # --- feeds -----------------------------------------------------------
    def load_feed(self, name):
        g = self.grids[name]
        if name == "home":
            def fn():
                items = [i for i in parse_items(
                    innertube("browse", browseId="FEwhat_to_watch"))
                    if i["kind"] in ("video", "short")]
                if not any(i["kind"] == "video" for i in items):
                    items = [i for i in parse_items(
                        innertube("search", query="trending today"))
                        if i["kind"] == "video"]
                return items
            g.load(fn)
        elif name == "shorts":
            g.load(self.shorts_feed, "No shorts returned.")
        elif name == "posts":
            g.load(lambda: self.from_subs(("posts", "community"), "post", 5),
                   "Community posts from channels you subscribe to show up "
                   "here. Subscribe to some channels (or sign in) first.")
        elif name == "subs":
            def fn():
                vids = []
                if logged_in():
                    try:
                        vids = [i for i in parse_items(innertube(
                            "browse", browseId="FEsubscriptions"))
                            if i["kind"] == "video"]
                    except Exception:  # noqa: BLE001
                        pass
                if not vids:
                    vids = self.from_subs(("videos",), "video", 4)
                ensure_avatars(list(self.subs.d))  # profile pictures
                chans = [{"kind": "channel", "id": c, "title": n, "channel": n,
                          "channel_id": c, "meta": "",
                          "thumb": AVATARS.get(c, "")}
                         for c, n in self.subs.d.items()]
                return chans + vids
            g.load(fn, "No subscriptions yet - open a video or channel and "
                       "press Subscribe, or sign in.")

    def shorts_feed(self):
        items, seen = [], set()
        try:
            for i in parse_items(innertube("browse", browseId="FEshorts")):
                if i["kind"] == "short" and i["id"] not in seen:
                    seen.add(i["id"])
                    items.append(i)
        except Exception:  # noqa: BLE001
            pass
        if len(items) < 12:
            def q(text):
                try:
                    return parse_items(innertube("search", query=text))
                except Exception:  # noqa: BLE001
                    return []
            queries = ["#shorts", "#shorts funny", "#shorts music",
                       "#shorts gaming", "#shorts trending", "#shorts food"]
            with ThreadPoolExecutor(6) as ex:
                results = list(ex.map(q, queries))
            for res in results:
                for i in res:
                    if i["id"] in seen:
                        continue
                    if i["kind"] == "short" or (i["kind"] == "video"
                                                and 0 < i.get("dur", 0) <= 60):
                        i["kind"] = "short"
                        seen.add(i["id"])
                        items.append(i)
        return items

    def from_subs(self, tabs, kind, per):
        ids = list(self.subs.d)[:12]
        if not ids:
            return []
        with ThreadPoolExecutor(6) as ex:
            results = list(ex.map(lambda c: self._safe_chan(c, tabs), ids))
        out = []
        for items in results:
            out += [i for i in items if i["kind"] == kind][:per]
        return out

    @staticmethod
    def _safe_chan(cid, tabs):
        try:
            name, items = channel_fetch(cid, tabs)
            for i in items:
                if not i.get("channel"):
                    i["channel"] = name
            return items
        except Exception:  # noqa: BLE001
            return []


class App(Gtk.Application):
    def __init__(self):
        super().__init__(application_id="org.vasik96.GtkTube")

    def do_activate(self):
        tame_gst_decoders()
        prov = Gtk.CssProvider()
        prov.load_from_data(CSS)
        Gtk.StyleContext.add_provider_for_display(
            Gdk.Display.get_default(), prov,
            Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
        window = self.props.active_window
        if window is None:
            window = Window(self)
            window.present()
            window.restore_window_state()
        else:
            window.present()


if __name__ == "__main__":
    sys.exit(App().run(sys.argv))