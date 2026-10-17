#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

TOOLCHAIN_REV="$(cut -f 2 -d: lean-toolchain)"

if [ ! -f docbuild/lakefile.toml ]; then
  mkdir -p docbuild
  cp lean-toolchain docbuild/lean-toolchain
  cat << EOF > docbuild/lakefile.toml
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "cft"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "$TOOLCHAIN_REV"
EOF
  (cd docbuild && MATHLIB_NO_CACHE_ON_UPDATE=1 lake update cft)
fi

(cd docbuild && lake build CFT:docs)

DOC_DIR="docbuild/.lake/build/doc"

if ! grep -q 'not(\[data-path="./CFT.html"\])' "$DOC_DIR/style.css"; then
  cat << 'EOF' >> "$DOC_DIR/style.css"

/* Hide external dependency libraries in the sidebar and keep only CFT */
.module_list > details.nav_sect:not([data-path="./CFT.html"]) {
  display: none !important;
}
EOF
fi

sed -i.bak 's|<details class="nav_sect" data-path="./CFT.html">|<details class="nav_sect" data-path="./CFT.html" open>|g' "$DOC_DIR/navbar.html"
rm -f "$DOC_DIR/navbar.html.bak"

echo ""
echo "Documentation built in $DOC_DIR"
echo "To preview locally, run:"
echo "  python3 -m http.server 8000 --directory $DOC_DIR"
echo "and open http://localhost:8000/CFT.html"

if [[ "${1:-}" == "--serve" ]]; then
  echo ""
  echo "Serving at http://localhost:8000/CFT.html (Ctrl+C to stop)..."
  python3 -m http.server 8000 --directory "$DOC_DIR"
fi

