#!/bin/bash
set -e  # Exit immediately if a command exits with a non-zero status

# App configuration
APP_NAME="GtkTube"
APP_ID="org.vasik96.GtkTube"
APPDIR="${APP_NAME}.AppDir"
APPIMAGE_TOOL="./appimagetool-x86_64.AppImage"

# Ensure appimagetool exists
if [ ! -f "$APPIMAGE_TOOL" ]; then
    echo "Downloading appimagetool..."
    wget -q "https://github.com/AppImage/AppImageKit/releases/download/continuous/appimagetool-x86_64.AppImage"
    chmod +x "$APPIMAGE_TOOL"
fi

echo "Cleaning up previous build files..."
rm -rf "$APPDIR" "${APP_NAME}"*.AppImage

echo "Creating AppDir directory structure..."
mkdir -p "$APPDIR/usr/bin"
mkdir -p "$APPDIR/usr/share/applications"
mkdir -p "$APPDIR/usr/share/icons/hicolor/scalable/apps"

echo "Copying source files into AppDir..."
# Main executable and Python files
cp main.py "$APPDIR/usr/bin/"
[ -f main_webplayer.py ] && cp main_webplayer.py "$APPDIR/usr/bin/"

# Metadata files
cp "${APP_ID}.desktop" "$APPDIR/usr/share/applications/"
cp "${APP_ID}.svg" "$APPDIR/usr/share/icons/hicolor/scalable/apps/"

# Root-level AppImage requirements
cp "${APP_ID}.desktop" "$APPDIR/${APP_ID}.desktop"
cp "${APP_ID}.svg" "$APPDIR/${APP_ID}.svg"

echo "Generating AppRun entrypoint script..."
cat << 'EOF' > "$APPDIR/AppRun"
#!/bin/sh
HERE="$(dirname "$(readlink -f "$0")")"
export PATH="${HERE}/usr/bin:${PATH}"
export PYTHONPATH="${HERE}/usr/bin:${PYTHONPATH}"

exec python3 "${HERE}/usr/bin/main.py" "$@"
EOF

chmod +x "$APPDIR/AppRun"

echo "Building AppImage..."
ARCH=x86_64 "$APPIMAGE_TOOL" "$APPDIR" "${APP_NAME}-x86_64.AppImage"

echo ""
echo "Done! Generated AppImage: ${APP_NAME}-x86_64.AppImage"
