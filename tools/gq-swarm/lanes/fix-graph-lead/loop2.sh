#!/usr/bin/env bash
# fix-graph-lead maintenance loop, v2 (for gqprobe-lean.sh v4 batched probes). 15-minute ticks, up to 12 h.
#  A. Consume new verdicts in $GQ/state/pq/*.{fix-graph-lead,fix-bh-a}/result, reading per-module build lines from the
#     remote per-request log (the batch id comes from sacct SubmitLine).
#     - PENDING (sweep-landed unwired) module red  -> new Cairn fix node, board line OPEN.
#     - PENDING module green                       -> board line GREEN.
#     - OPEN module green, same bytes as main      -> node RESOLVED, board line RESOLVED.
#     - OPEN module still red after a change       -> node's first-error block refreshed.
#     A green counts only if no other request in the same batch overlaid a file in the module's import closure
#     (v4 builds "main + pending fixes"), since such a green would be about a different tree.
#  B. At most every 45 min, if no request of this lane is in flight: probe the OPEN modules whose main bytes changed
#     since they were last seen red (one background gqprobe-lean.sh request, empty overlay).
set -uo pipefail
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
W=$GQ/work/fix-graph-lead; B=$GQ/board/FIX-GRAPH.md; PQ=$GQ/state/pq; REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi; PHOME=/projects/standard/hsiehph/sauer354
LOG=$W/loop.log; SEEN=$W/seen-results.txt; LAST=$W/last-red-blob.tsv; LASTPROBE=$W/last-probe-epoch
touch $SEEN $LAST; : > $W/overlay.files; [ -f $LASTPROBE ] || echo 0 > $LASTPROBE
cd $REPO || exit 2
say() { echo "$(date '+%F %T') $*" >> $LOG; }
m2p() { echo "$(echo "$1" | tr . /).lean"; }
p2m() { echo "${1%.lean}" | tr / .; }
msi() { "$MSI" "$@" < /dev/null 2>&1 | tr -d '\r'; }
closure() { # $1 base sha, $2 path -> import closure paths (GroupApproximation only)
  local base=$1 fr seen nx; fr=$(mktemp); seen=$(mktemp); nx=$(mktemp); echo "$2" > $fr
  while [ -s $fr ]; do cat $fr >> $seen; : > $nx
    while read -r p; do git show "$base:$p" 2>/dev/null | awk '/^import GroupApproximation/{print $2}' | while read -r m; do m2p "$m"; done >> $nx; done < $fr
    sort -u $nx | comm -23 - <(sort -u $seen) > $fr; done
  sort -u $seen; rm -f $fr $seen $nx
}
refresh_or_resolve() { # $1 id $2 mode(RESOLVE|REFRESH) $3 base $4 jid $5 errs-file
  local f=$W/research/$1.md
  git show refs/remotes/origin/main:research/$1.md > $f 2>/dev/null || return 1
  if [ "$2" = RESOLVE ]; then
    perl -0pi -e "s/^\*\*OPEN\.\*\*/**RESOLVED (${3:0:10}, trusted batched probe job $4).** Previously OPEN./m" $f
  else
    ERRS="$(cat $5)" JID=$4 BASE=${3:0:10} perl -0pi -e 's/\*\*First errors \(verbatim\)\.\*\*\n\n```\n.*?\n```/**First errors (verbatim; refreshed from probe job $ENV{JID} on main $ENV{BASE}).**\n\n```\n$ENV{ERRS}\n```/s' $f
  fi
}
new_node() { # $1 path $2 owner $3 jid $4 errs-file -> prints id
  local p=$1 m s id short; m=$(p2m "$p"); s=${p#GroupApproximation/}; s=${s%.lean}
  id="fix-$(echo "$s" | sed -E 's/([a-z0-9])([A-Z])/\1-\2/g; s/([A-Z])([A-Z][a-z])/\1-\2/g' | tr 'A-Z/_' 'a-z--' | tr -s '-' | cut -c1-60 | sed 's/-$//')"
  short=$(head -1 $4 | sed -E 's/^error: [^ ]+: //' | tr -d '"`' | cut -c1-70)
  { echo "---"; echo "rg: 2"; echo "id: $id"; echo "kind: route"; echo "title: \"Fix $m: ${short:-build failure}\""; echo "---"; echo
    echo "**OPEN.** Lean module \`$p\` is unwired: the 09-18 coordinator sweep landed it with red allowed. It fails its trusted batched probe (Slurm job $3)."
    echo "It is part of the Cairn fix graph (index \`board/FIX-GRAPH.md\` in the swarm workspace). Owner: $2."
    echo; echo "**First errors (verbatim).**"; echo; echo '```'; if [ -s $4 ]; then cat $4; else echo "(no error line in this file: an import failed to build)"; fi; echo '```'
    echo; echo "**What it needs.** Make \`$m\` compile under the repository settings without changing any statement. The root does not import it, so nothing else is blocked on it."
    echo; echo "**Resolution.** When a trusted probe builds it green, change the status line above to \`**RESOLVED (<green commit>).**\`."
  } > $W/research/$id.md
  echo "$id"
}

for tick in $(seq 1 48); do
  # ---- A. consume verdicts
  for r in $(ls -d $PQ/*.fix-graph-lead $PQ/*.fix-bh-a 2>/dev/null); do
    [ -f $r/result ] || continue; grep -qxF "$r" $SEEN && continue
    echo "$r" >> $SEEN
    V=$(head -1 $r/result); L=$(echo "$V" | grep -oE 'log=[^ ]+' | cut -d= -f2)
    jid=$(echo "$V" | grep -oE 'job=[0-9]+' | cut -d= -f2)
    if [ -s $r/overlay.md5 ]; then say "skip $r: own overlay non-empty"; continue; fi
    if [ -z "$jid" ] || [ ! -f "$L" ]; then say "skip $r: $(echo "$V" | cut -c1-90)"; continue; fi
    base=$(sed -n '1s/^base \([0-9a-f]*\);.*/\1/p' "$L"); n=$(sed -n '1s/.*batch job [0-9]* (\([0-9]*\) of.*/\1/p' "$L")
    sub=$(msi "sacct -j $jid -X -n -P -o SubmitLine | head -1"); bat=$(echo "$sub" | grep -oE 'batch-b[0-9]+' | head -1)
    [ -n "$bat" ] && [ -n "$n" ] || { say "skip $r: cannot locate remote log (sub='$sub')"; sed -i '' "\|^$r\$|d" $SEEN; continue; }
    RL=$PHOME/gq-slurm/$bat-$n.log
    RAW=$(msi "grep -aE 'Built |Replayed |✖|^error: ' $RL | head -6000; echo SENTINEL")
    echo "$RAW" | grep -q SENTINEL || { say "skip $r: remote log unreadable"; sed -i '' "\|^$r\$|d" $SEEN; continue; }
    # other overlays in the same batch
    OTHER=$(grep -l "job=$jid" $PQ/*/result 2>/dev/null | while read -r x; do d=$(dirname $x); [ "$d" = "$r" ] || awk '{print $2}' $d/overlay.md5; done | sort -u)
    say "verdicts for $(basename $r) job $jid ($bat-$n) base ${base:0:10}; other overlays: $(echo "$OTHER" | grep -c .)"
    NEWP=""; EDITP=""; RES_IDS=""
    for m in $(cat $r/targets); do
      p=$(m2p "$m")
      if echo "$RAW" | grep -qE "^error: $p:|✖.* $m( |\$)"; then v=RED
      elif echo "$RAW" | grep -qE "(Built|Replayed) $m( |\$)"; then v=GREEN
        if [ -n "$OTHER" ] && closure "$base" "$p" | grep -qxF -f <(echo "$OTHER"); then v=GREEN_WITH_PENDING; fi
      else v=UNKNOWN; fi
      echo "$RAW" | grep -E "^error: $p:" | head -4 | cut -c1-220 > $W/errs.tmp
      if grep -qE "^PENDING $p " $B; then
        own=$(awk -v p="$p" '$1=="PENDING" && $2==p{print $3}' $B)
        if [ $v = RED ]; then id=$(new_node "$p" "$own" "$jid" $W/errs.tmp); NEWP="$NEWP research/$id.md"
          sed -i '' "s|^PENDING $p $own\$|OPEN $id $m $own|" $B; echo "$p $(git rev-parse -q --verify $base:$p)" >> $LAST
        elif [ $v = GREEN ]; then sed -i '' "s|^PENDING $p $own\$|GREEN $p $own (job $jid, ${base:0:10})|" $B; fi
      elif grep -qE "^OPEN [^ ]+ $m " $B; then
        id=$(awk -v m="$m" '$1=="OPEN" && $3==m{print $2}' $B)
        same=no; [ "$(git rev-parse -q --verify refs/remotes/origin/main:$p)" = "$(git rev-parse -q --verify $base:$p)" ] && same=yes
        if [ $v = GREEN ] && [ $same = yes ]; then refresh_or_resolve $id RESOLVE $base $jid /dev/null && { EDITP="$EDITP research/$id.md"; RES_IDS="$RES_IDS $id"; }
        elif [ $v = RED ]; then
          sed -i '' "\|^$p |d" $LAST; echo "$p $(git rev-parse -q --verify $base:$p)" >> $LAST
          [ -s $W/errs.tmp ] && refresh_or_resolve $id REFRESH $base $jid $W/errs.tmp && EDITP="$EDITP research/$id.md"
        fi
      fi
      say "  $m $v"
    done
    if [ -n "$NEWP$EDITP" ]; then
      printf 'Cairn fix graph: update from trusted batched probe job %s\n\nNew fix nodes for red unwired modules, RESOLVED for modules that built green on main, and refreshed first errors for modules still red after repairs.\n' "$jid" > $GQ/msgs/fix-graph-lead-loop.txt
      # shellcheck disable=SC2086
      out=$(GQ_BASE=$(git rev-parse refs/remotes/origin/main) GQ_BASE_PATHS="$EDITP" timeout 900 bash $GQ/gqland.sh fix-graph-lead $GQ/msgs/fix-graph-lead-loop.txt $NEWP $EDITP 2>&1 | grep -E 'LANDED|REFUSED' | head -2)
      say "land: $out"
      if echo "$out" | grep -q LANDED; then sha=$(echo "$out" | grep -oE 'LANDED [0-9a-f]+' | cut -d' ' -f2)
        for id in $RES_IDS; do sed -i '' "s|^OPEN $id \(.*\)\$|RESOLVED $id \1 (${sha:0:10})|" $B; done; fi
    fi
  done
  # ---- B. probe changed OPEN modules (at most every 45 min, one request in flight)
  inflight=$(for d in $(ls -d $PQ/*.fix-graph-lead 2>/dev/null); do [ -f $d/result ] || echo $d; done | head -1)
  now=$(date +%s)
  if [ -z "$inflight" ] && [ $((now - $(cat $LASTPROBE))) -ge 2700 ]; then
    T=""
    for m in $(awk '$1=="OPEN"{print $3}' $B); do p=$(m2p "$m"); old=$(awk -v p="$p" '$1==p{print $2}' $LAST | tail -1)
      [ "$(git rev-parse -q --verify refs/remotes/origin/main:$p)" != "${old:-x}" ] && T="$T $m"; done
    if [ -n "$T" ]; then echo $now > $LASTPROBE; say "probe request:$T"
      # shellcheck disable=SC2086
      nohup bash $GQ/gqprobe-lean.sh fix-graph-lead $T > $W/probe-last.out 2>&1 &
    fi
  fi
  sleep 900
done
say "loop2 finished"
