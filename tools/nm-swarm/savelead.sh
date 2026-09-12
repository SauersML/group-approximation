#!/usr/bin/env bash
# savelead.sh <msg>  -- USER ORDER 09-11 22:45 "an edit NOT pushed and committed to main is UNSAVED":
# copy the lead's swarm infra + census rows + lane reports into the repo (MSI identifiers scrubbed, since the
# pre-commit policy bans the login host/user) and land them on origin/main through nmland.sh (clobber-guarded).
set -uo pipefail
NM=/private/tmp/claude-501/-Users-user-nonsofic-existence/77122910-de5a-4e59-a488-7cea550292c5/scratchpad/nm
REPO=/Users/user/nonsofic_existence
MSG=${1:-"Save the non-MF swarm infrastructure, census rows and lane reports"}
scrub() { sed -e 's/__MSI_USER__/__MSI_USER__/g' -e 's/__MSI_GROUP__/__MSI_GROUP__/g' -e 's/login\.msi\.umn\.edu/__MSI_LOGIN__/g' -e 's/[0-9]\{1,3\}\.[0-9]\{1,3\}\.[0-9]\{1,3\}\.[0-9]\{1,3\}/__IP__/g' "$1"; }
PATHS=()
put() {  # put <src> <repo-dest>
  local src=$1 dst=$REPO/$2
  [ -f "$src" ] || return 0
  mkdir -p "$(dirname "$dst")"; scrub "$src" > "$dst.tmp" && mv "$dst.tmp" "$dst"; PATHS+=("$2")
}
for f in COMMON_RULES.md LIX_LANES.md wire-queue.txt wave1.mods wave2.mods census-notes.md WORKLIST.md landed.log atrisk.txt deprecated-at-pin.txt; do put "$NM/$f" "notes/nm-swarm/$f"; done
for f in "$NM"/rows/*.tsv; do put "$f" "metadata/nm-census-rows/$(basename "$f")"; done
for f in "$NM"/reports/*.md; do put "$f" "notes/nm-swarm/reports/$(basename "$f")"; done
for f in nmprobe.sh nmland.sh nmwire.sh nmwirelist.sh closure.sh savelead.sh palomar-verify.sh dupcheck.py; do put "$NM/$f" "tools/nm-swarm/$f"; done
for f in "$NM"/remote/*.sh "$NM"/remote/*.py; do put "$f" "tools/nm-swarm/remote/$(basename "$f")"; done
for f in "$NM"/census/*.sh "$NM"/census/*.py; do put "$f" "tools/nm-swarm/census/$(basename "$f")"; done
for lf in "$NM"/lanes/*.files "$NM"/lanes/*.clone; do put "$lf" "notes/nm-swarm/lanes/$(basename "$lf")"; done
cd "$REPO" || exit 2
if grep -lE '__MSI_USER__|__MSI_GROUP__|umn\.edu' ${PATHS[@]+"${PATHS[@]}"} 2>/dev/null; then echo "REFUSED: unscrubbed identifier"; exit 2; fi
printf '%s\n\nScrubbed copies (MSI host/user/group replaced by placeholders) of the lead scratchpad: COMMON_RULES,\nLIX lane table, wiring queue, landing log, per-lane census rows, lane reports and the probe/land/wire scripts.\n' "$MSG" > "$NM/msgs/savelead.msg"
bash "$NM/nmland.sh" lead "$NM/msgs/savelead.msg" ${PATHS[@]+"${PATHS[@]}"}
