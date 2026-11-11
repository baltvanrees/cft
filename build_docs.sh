#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

DOC_DIR="$(lake query :literateHtml)"

echo ""
echo "Documentation built in $DOC_DIR"
echo "To preview locally, run:"
echo "  ./build_docs.sh --serve"
echo "or:"
echo "  python3 -m http.server 8000 --directory $DOC_DIR"
echo "and open http://localhost:8000/"

if [[ "${1:-}" == "--serve" ]]; then
  echo ""
  echo "Serving at http://localhost:8000/ (Ctrl+C to stop)..."
  python3 -m http.server 8000 --directory "$DOC_DIR"
fi
