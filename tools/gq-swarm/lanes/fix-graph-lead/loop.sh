#!/usr/bin/env bash
# fix-graph-lead maintenance loop: runs every ~45 min, up to 16 cycles.
#   A. Consume new probe results: fix-bh-a's probes of sweep-landed unwired Lean, and our own.
#      A PENDING module found red gets a new Cairn fix node (OPEN). A green one is marked GREEN on the board.
#   B. Probe the OPEN red modules whose source on origin/main changed since they were last seen red,
#      with one gqprobe-lean.sh run and an empty overlay. Modules that build green get RESOLVED.
# Never builds locally, never fetches (gqprobe-lean.sh and gqland.sh refresh origin themselves), never touches the root.
set -uo pipefail
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
W=$GQ/work/fix-graph-lead; B=$GQ/board/FIX-GRAPH.md; REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi; PHOME=/projects/standard/hsiehph/sauer354
LOG=$W/loop.log; SEEN=$W/seen-logs.txt; LAST=$W/last-red-blob.tsv
touch $SEEN $LAST; : > $W/overlay.files
cd $REPO || exit 2
say() { echo "$(date '+%F %T') $*" >> $LOG; }
p2m() { echo "${1%.lean}" | tr / .; }
m2p() { echo "$(echo "$1" | tr . /).lean"; }
blob() { git rev-parse -q --verify "refs/remotes/origin/main:$1" 2>/dev/null || echo NONE; }
# baseline: every OPEN module was red at 3c8b417428
if [ ! -s $LAST ]; then
  awk '$1=="OPEN"{print $3}' $B | while read -r m; do p=$(m2p "$m"); echo "$p $(git rev-parse -q --verify 3c8b417428:$p)"; done > $LAST
fi

# fetch per-module verdicts from a finished Slurm probe job: prints "<module> GREEN|RED"
verdicts() { # $1 lane, $2 jid, $3.. modules
  local lane=$1 jid=$2; shift 2
  local R; R=$("$MSI" "grep -aE 'Built |Replayed |✖|^error: ' $PHOME/gq-slurm/probe-$lane-$jid.log | head -4000; echo SENTINEL" < /dev/null 2>&1 | tr -d '\r')
  echo "$R" | grep -q SENTINEL || return 1
  for m in "$@"; do
    p=$(m2p "$m")
    if echo "$R" | grep -qE "^error: $p:|✖.* $m( |\$)"; then echo "$m RED"
    elif echo "$R" | grep -qE "(Built|Replayed) $m( |\$)"; then echo "$m GREEN"
    else echo "$m UNKNOWN"; fi
  done
}
first_errors() { # $1 lane $2 jid $3 path
  "$MSI" "grep -a '^error: $3:' $PHOME/gq-slurm/probe-$1-$2.log | head -4 | cut -c1-220" < /dev/null 2>&1 | tr -d '\r' | grep '^error:'
}
land_nodes() { # $1 msg, rest paths (under $W); GQ_BASE for edits
  local msg=$1; shift
  GQ_BASE=$(git rev-parse refs/remotes/origin/main) GQ_BASE_PATHS="$*" timeout 900 bash $GQ/gqland.sh fix-graph-lead "$msg" "$@" 2>&1 | grep -E 'LANDED|REFUSED' | head -2
}
resolve_node() { # $1 node id, $2 green base sha, $3 jid
  local id=$1 f=$W/research/$1.md
  git show refs/remotes/origin/main:research/$id.md > $f 2>/dev/null || return 1
  perl -0pi -e "s/^\*\*OPEN\.\*\*/**RESOLVED (${2:0:10}, trusted probe job $3).** Previously OPEN./m" $f
}
new_node() { # $1 lane $2 jid $3 path $4 owner
  local p=$3 m; m=$(p2m "$3")
  local s=${p#GroupApproximation/}; s=${s%.lean}
  local id; id="fix-$(echo "$s" | sed -E 's/([a-z0-9])([A-Z])/\1-\2/g; s/([A-Z])([A-Z][a-z])/\1-\2/g' | tr 'A-Z/_' 'a-z--' | tr -s '-' | cut -c1-60 | sed 's/-$//')"
  local errs; errs=$(first_errors "$1" "$2" "$p")
  local short; short=$(echo "$errs" | head -1 | sed -E 's/^error: [^ ]+: //' | tr -d '"`' | cut -c1-70)
  { echo "---"; echo "rg: 2"; echo "id: $id"; echo "kind: route"; echo "title: \"Fix $m: ${short:-build failure}\""; echo "---"; echo
    echo "**OPEN.** Lean module \`$p\` is an unwired module (landed by the 09-18 coordinator sweep, red allowed) and fails its trusted probe (Slurm job $2)."
    echo "Part of the Cairn fix graph (index \`board/FIX-GRAPH.md\` in the swarm workspace). Owner: $4."
    echo; echo "**First errors (verbatim).**"; echo; echo '```'; echo "${errs:-(no error line in this file: an import failed; see the probe log)}"; echo '```'
    echo; echo "**What it needs.** Make \`$m\` compile with the repository settings, changing no statement. It is not imported by the root, so nothing else is blocked on it."
    echo; echo "**Resolution.** When a trusted probe builds it green, change the status line above to \`**RESOLVED (<green commit>).**\`."
  } > $W/research/$id.md
  echo "$id"
}

for cycle in $(seq 1 16); do
  say "cycle $cycle"
  # A. consume unseen finished probe logs of fix-bh-a and of this lane
  for L in $(ls -t $GQ/state/probe-logs/fix-bh-a.*.log $GQ/state/probe-logs/fix-graph-lead.*.log 2>/dev/null); do
    grep -qxF "$L" $SEEN && continue
    jid=$(grep -oE 'submitted Slurm job [0-9]+' "$L" | grep -oE '[0-9]+$' | tail -1)
    grep -qE '^job [0-9]+ state (COMPLETED|FAILED|TIMEOUT|OUT_OF_MEMORY|CANCELLED)' "$L" || continue
    echo "$L" >> $SEEN
    [ -n "$jid" ] || continue
    lane=$(basename "$L" | cut -d. -f1)
    base=$(sed -n 's/^base \([0-9a-f]*\);.*/\1/p' "$L" | head -1)
    mods=$(sed -n 's/^base [0-9a-f]*; overlay [0-9]* files; targets //p' "$L" | head -1)
    ov=$(sed -n 's/^base [0-9a-f]*; overlay \([0-9]*\) files.*/\1/p' "$L" | head -1)
    [ "${ov:-1}" = 0 ] || { say "skip $L: overlay non-empty (not a build of main)"; continue; }
    # shellcheck disable=SC2086
    V=$(verdicts "$lane" "$jid" $mods) || { say "could not read job $jid log"; sed -i '' "\|^$L\$|d" $SEEN; continue; }
    say "job $jid ($lane) base ${base:0:10}: $(echo "$V" | awk '{c[$2]++} END{for(k in c) printf "%s=%d ", k, c[k]}')"
    NEWP=""; RESP=""; RES_IDS=""
    while read -r m v; do
      p=$(m2p "$m")
      if grep -qE "^PENDING $p " $B; then
        own=$(awk -v p="$p" '$1=="PENDING" && $2==p{print $3}' $B)
        if [ "$v" = RED ]; then id=$(new_node "$lane" "$jid" "$p" "$own"); NEWP="$NEWP research/$id.md"
          sed -i '' "s|^PENDING $p $own\$|OPEN $id $m $own|" $B
        elif [ "$v" = GREEN ]; then sed -i '' "s|^PENDING $p $own\$|GREEN $p $own (job $jid, ${base:0:10})|" $B; fi
      elif grep -qE "^OPEN [^ ]+ $m " $B && [ "$v" = GREEN ] && [ "$(blob "$p")" = "$(git rev-parse -q --verify "$base:$p")" ]; then
        id=$(awk -v m="$m" '$1=="OPEN" && $3==m{print $2}' $B)
        resolve_node "$id" "$base" "$jid" && { RESP="$RESP research/$id.md"; RES_IDS="$RES_IDS $id"; }
      elif [ "$v" = RED ]; then sed -i '' "\|^$p |d" $LAST; echo "$p $(blob "$p")" >> $LAST; fi
    done <<< "$V"
    if [ -n "$NEWP$RESP" ]; then
      printf 'Cairn fix graph: update from trusted probe job %s\n\nNew fix nodes for red unwired modules; RESOLVED status for modules that built green on main.\n' "$jid" > $GQ/msgs/fix-graph-lead-loop.txt
      # new nodes are new paths; resolved ones are GQ_BASE edits
      # shellcheck disable=SC2086
      r=$(land_nodes $GQ/msgs/fix-graph-lead-loop.txt $NEWP $RESP); say "land: $r"
      if echo "$r" | grep -q LANDED; then sha=$(echo "$r" | grep -oE 'LANDED [0-9a-f]+' | cut -d' ' -f2)
        for id in $RES_IDS; do sed -i '' "s|^OPEN $id |RESOLVED $id |" $B; sed -i '' "/^RESOLVED $id / s|\$| (${sha:0:10})|" $B; done; fi
    fi
  done
  # B. probe OPEN modules whose source changed since last seen red
  T=""
  for m in $(awk '$1=="OPEN"{print $3}' $B); do
    p=$(m2p "$m"); old=$(awk -v p="$p" '$1==p{print $2}' $LAST)
    [ "$(blob "$p")" != "${old:-x}" ] && T="$T $m"
  done
  if [ -n "$T" ]; then
    say "probing changed OPEN modules:$T"
    # shellcheck disable=SC2086
    bash $GQ/gqprobe-lean.sh fix-graph-lead $T > $W/probe-last.out 2>&1
    say "probe: $(grep -E '^PROBE' $W/probe-last.out | head -1 | cut -c1-120)"
    continue   # results are consumed at the top of the next cycle, without the sleep
  else say "no OPEN module changed on main; no probe"; fi
  sleep 2700
done
say "loop finished"
