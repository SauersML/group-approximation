#!/usr/bin/env bash
# Install the PR-only loader into ~/.grok/hooks/, which is the only hook
# location Grok 0.2.93 actually reads. The loader is repository-agnostic: it
# runs this repository's guard here and does nothing at all anywhere else, so
# it is safe to leave installed permanently.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
dest="${HOME}/.grok/hooks"
mkdir -p "$dest"
install -m 0644 "$here/hooks/global-loader.json" "$dest/pr-only.json"
python3 -c "import json,sys;json.load(open(sys.argv[1]))" "$dest/pr-only.json"
echo "installed $dest/pr-only.json"
echo "verify with: grok inspect   (expect a 'command ... user' entry under Hooks)"
