#!/usr/bin/env bash
# fix-graph-lead maintenance loop v3 (main-only, gqprobe-lean.sh v4 batched). 10-min ticks, up to 12 h.
# Restart after a session restart with:  bash $GQ/work/fix-graph-lead/loop3.sh   (Bash run_in_background)
#
# A. Consume every finished probe request in $GQ/state/pq whose own overlay is EMPTY, from any lane: such a
#    request builds origin/main at its base, apart from the other overlays in the same batch.
#    Per module, from the remote per-request log (lake prints nothing for modules that build or are cached):
#      RED      "✖ … Building M" or an "error: <path>:" line for M
#      BLOCKED  not red itself, but its import closure reaches red modules (DEPS = the nearest ones)
#      GREEN    request rc 0, or the build ran to its end ("build failed" summary) and M is neither red nor blocked
#      UNKNOWN  otherwise (incomplete or timed-out build), or another request in the batch overlaid a file in M's
#               import closure, so the verdict would be about a different tree
#    Actions: PENDING red/blocked -> new fix node (requires = nodes of DEPS). PENDING green -> GREEN.
#    OPEN green -> RESOLVED. OPEN red -> first errors refreshed. OPEN blocked -> requires set.
#    A red module that is not on the board (a gap) -> new fix node. Any verdict is dropped (UNKNOWN_STALE) when a file
#    in the module's import closure changed on main since the probe's base.
# B. At most every 45 min, with no request of this lane in flight: probe OPEN modules whose bytes changed since last
#    seen red or blocked, or whose verdict was UNKNOWN, plus all PENDING modules. Grouped requests, empty overlay.
set -uo pipefail
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
W=$GQ/work/fix-graph-lead; B=$GQ/board/FIX-GRAPH.md; PQ=$GQ/state/pq; REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi; PHOME=/projects/standard/hsiehph/sauer354; M=refs/remotes/origin/main
LOG=$W/loop.log; SEEN=$W/seen-results3.txt; LAST=$W/last-red-blob.tsv; UNK=$W/unknown.txt; BLK=$W/blocked.txt
LASTPROBE=$W/last-probe-epoch; T0=$(date +%s)
touch $SEEN $LAST $UNK $BLK; : > $W/overlay.files; [ -f $LASTPROBE ] || echo 0 > $LASTPROBE
cd $REPO || exit 2
say() { echo "$(date '+%F %T') $*" >> $LOG; }
m2p() { echo "$(echo "$1" | tr . /).lean"; }
p2m() { echo "${1%.lean}" | tr / .; }
msi() { "$MSI" "$@" < /dev/null 2>&1 | tr -d '\r'; }
blob() { git rev-parse -q --verify "$1:$2" 2>/dev/null || echo NONE; }
edges() { # $1 base -> edge file "from to" (paths)
  local f=$W/edges.$1
  [ -s $f ] || git grep '^import GroupApproximation' $1 -- 'GroupApproximation/*.lean' | sed -E "s|^[^:]+:([^:]+):import (.*)$|\1 \2|" \
    | awk '{gsub(/\./,"/",$2); print $1, $2".lean"}' > $f
  echo $f
}
closure() { # $1 edgefile $2 start path -> all paths reachable (incl. start)
  awk -v s="$2" '{adj[$1]=adj[$1]" "$2} END{q[1]=s; seen[s]=1; h=1; t=1; while(h<=t){f=q[h++]; n=split(adj[f],a," "); for(i=1;i<=n;i++) if(!(a[i] in seen)){seen[a[i]]=1; q[++t]=a[i]}} for(k in seen) print k}' $1
}
nearest_red() { # $1 edgefile $2 start $3 redfile -> red paths reached without passing through another red path
  awk -v s="$2" 'FILENAME==ARGV[1]{red[$1]=1; next} {adj[$1]=adj[$1]" "$2} END{q[1]=s; seen[s]=1; h=1; t=1; while(h<=t){f=q[h++]; n=split(adj[f],a," "); for(i=1;i<=n;i++) if(!(a[i] in seen)){seen[a[i]]=1; if(a[i] in red) print a[i]; else q[++t]=a[i]}}}' $3 $1
}
owner() { # path -> lane
  case "$1" in
    GroupApproximation/BooneHigman/Metabelian/*) echo bh-pal-wire; return;;
    GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/*|GroupApproximation/Manuscript/SimpleKazhdanSofic/SkRows/*) echo ms-green-sk; return;;
  esac
  local d o=""; d=$(dirname "$1")
  while [ -z "$o" ] && [ "$d" != GroupApproximation ] && [ "$d" != . ]; do
    o=$(awk -F'\t' -v d="$d" '$2=="lean"{x=$4; sub(/\/[^\/]*$/,"",x); if(x==d) print $3}' $GQ/state/unlanded2.tsv | sort | uniq -c | sort -rn | awk 'NR==1{print $2}')
    d=$(dirname "$d")
  done
  case "$o$1" in GroupApproximation/Manuscript/NonMF/*) o=ms-green-nm;; esac
  echo "${o:-unowned}"
}
slug_id() { # path -> fix id, unique against main
  local s=${1#GroupApproximation/} id n=2; s=${s%.lean}
  s=$(echo "$s" | sed -e 's|^BooneHigman/Metabelian/|bhmet/|' -e 's|^Manuscript/SimpleKazhdanSofic/|sk/|' -e 's|^Manuscript/NonMF/|nm/|')
  id="fix-$(echo "$s" | sed -E 's/([a-z0-9])([A-Z])/\1-\2/g; s/([A-Z])([A-Z][a-z])/\1-\2/g' | tr 'A-Z/_' 'a-z--' | tr -s '-' | cut -c1-60 | sed 's/-$//')"
  local c=$id
  while git cat-file -e "$M:research/$c.md" 2>/dev/null && ! git show "$M:research/$c.md" | grep -qF "\`$1\`"; do c="$id-$n"; n=$((n+1)); done
  echo "$c"
}
id_of() { awk -v m="$1" '($1=="OPEN"||$1=="RESOLVED") && $3==m{print $2}' $B | head -1; }
set_requires() { # $1 file, rest ids
  local f=$1; shift; local R=""; for x in "$@"; do R="$R  - $x\n"; done
  REQ="$R" perl -0pi -e 's/\A(---\n.*?)\nrequires:\n(?:  - [^\n]*\n)*/$1\n/s; s/\A(---\n.*?\n)---\n/$1 . ($ENV{REQ} ne "" ? "requires:\n$ENV{REQ}" : "") . "---\n"/se' $f
}
new_node() { # $1 path $2 owner $3 jid $4 base $5 errsfile $6.. required ids (non-empty => blocked-only if no errs)
  local p=$1 own=$2 jid=$3 base=$4 ef=$5 m id short; shift 5; m=$(p2m "$p"); id=$(slug_id "$p")
  short=$(head -1 $ef | sed -E 's/^error: [^ ]+: //' | tr -d '"`' | cut -c1-70); [ -z "$short" ] && short="fails through red imports"
  { echo "---"; echo "rg: 2"; echo "id: $id"; echo "kind: route"; echo "title: \"Fix $m: $short\""; echo "---"; echo
    echo "**OPEN.** Lean module \`$p\` is red on main at ${base:0:10} (trusted batched probe, Slurm job $jid, empty overlay). It is not in the root closure."
    echo "It is part of the Cairn fix graph (index \`board/FIX-GRAPH.md\` in the swarm workspace). Owner: $own."
    echo; echo "**First errors (verbatim).**"; echo; echo '```'
    if [ -s $ef ]; then cat $ef; else echo "(none in this file: it fails only because red imports fail; see requires)"; fi; echo '```'
    echo; echo "**What it needs.** Make \`$m\` compile under the repository settings without changing any statement."
    [ $# -gt 0 ] && echo "Its nearest red imports have their own fix nodes (listed in \`requires\`). Fix those first."
    echo; echo "**Resolution.** When a trusted probe builds it green, change the status line above to \`**RESOLVED (<green commit>).**\`."
  } > $W/research/$id.md
  [ $# -gt 0 ] && set_requires $W/research/$id.md "$@"
  echo "$id"
}

consume() { # $1 request dir
  local r=$1 V L jid base n rc bat RL RAW E OTHER R RS complete NEWP="" EDITP="" BOARD=$W/board-edits.sh RES=""
  V=$(head -1 $r/result); L=$(echo "$V" | grep -oE 'log=[^ ]+' | cut -d= -f2); jid=$(echo "$V" | grep -oE 'job=[0-9]+' | cut -d= -f2)
  [ -z "$jid" ] || [ ! -f "$L" ] && { say "skip $(basename $r): $(echo "$V" | cut -c1-80)"; return 0; }
  base=$(sed -n '1s/^base \([0-9a-f]*\);.*/\1/p' "$L"); n=$(sed -n '1s/.*batch job [0-9]* (\([0-9]*\) of.*/\1/p' "$L")
  rc=$(sed -n '1s/.*; rc \([0-9a-z]*\)$/\1/p' "$L")
  bat=$(msi "sacct -j $jid -X -n -P -o SubmitLine | head -1" | grep -oE 'batch-b[0-9]+' | head -1)
  [ -n "$bat" ] && [ -n "$n" ] && [ -n "$base" ] || { say "retry later $(basename $r): cannot locate remote log"; return 1; }
  RL=$PHOME/gq-slurm/$bat-$n.log
  RAW=$(msi "grep -aE '✖ |^error: GroupApproximation/|build failed|Build completed' $RL | cut -c1-240 | head -8000; echo SENTINEL")
  echo "$RAW" | grep -q SENTINEL || { say "retry later $(basename $r): remote log unreadable"; return 1; }
  E=$(edges $base); RS=$W/red.$jid.$n
  { echo "$RAW" | sed -nE 's/^✖ \[[0-9]+\/[0-9]+\] [A-Za-z]+ ([A-Za-z0-9_.]+).*/\1/p' | while read -r x; do m2p "$x"; done
    echo "$RAW" | sed -nE 's/^error: (GroupApproximation\/[^:]+\.lean):.*/\1/p'; } | sort -u > $RS
  complete=no; { [ "$rc" = 0 ] || echo "$RAW" | grep -qE 'build failed|Build completed'; } && complete=yes
  OTHER=$W/other.$jid.$n
  grep -l "job=$jid " $PQ/*/result 2>/dev/null | while read -r x; do d=$(dirname $x); [ "$d" = "$r" ] || awk '{print $2}' $d/overlay.md5; done | sort -u > $OTHER
  git diff --name-only $base $M -- GroupApproximation/ > $W/changed.$jid.$n
  say "consume $(basename $r) job $jid ($bat-$n) base ${base:0:10} rc ${rc:-?} complete=$complete red=$(wc -l < $RS | tr -d ' ') other-overlays=$(wc -l < $OTHER | tr -d ' ')"
  : > $BOARD
  # candidates: every red module in the log, then this request's targets
  { cat $RS; for t in $(cat $r/targets); do m2p "$t"; done; } | awk '!s[$0]++' > $W/cand.txt; : > $W/pass.txt
  while read -r p; do
    m=$(p2m "$p"); v=UNKNOWN; deps=""
    closure $E "$p" > $W/clo.tmp
    deps=$(nearest_red $E "$p" $RS | sort -u | tr '\n' ' ')
    echo "$RAW" | grep -F "error: $p:" | head -4 > $W/errs.tmp
    if [ -s $OTHER ] && grep -qxF -f $OTHER $W/clo.tmp; then v=UNKNOWN_BATCH
    elif [ -s $W/changed.$jid.$n ] && grep -qxF -f $W/changed.$jid.$n $W/clo.tmp; then v=UNKNOWN_STALE
    elif grep -qxF "$p" $RS; then v=RED; [ ! -s $W/errs.tmp ] && [ -n "$deps" ] && v=BLOCKED
    elif [ -n "$deps" ]; then v=BLOCKED
    elif [ $complete = yes ]; then v=GREEN; fi
    st=$(awk -v p="$p" -v m="$m" '($1=="PENDING" && $2==p) || (($1=="OPEN"||$1=="RESOLVED"||$1=="GREEN") && ($3==m || $2==p)){print $1; exit}' $B)
    case "$st:$v" in
      PENDING:RED|PENDING:BLOCKED|:RED|:BLOCKED)
        [ -z "$st" ] && [ "$v" = BLOCKED ] && continue  # a blocked non-target is not news
        own=$(awk -v p="$p" '$1=="PENDING" && $2==p{print $3}' $B); [ -n "$own" ] || own=$(owner "$p")
        id=$(new_node "$p" "$own" "$jid" "$base" $W/errs.tmp); NEWP="$NEWP research/$id.md"
        echo "$id|$p|$deps" >> $W/pass.txt
        if [ "$st" = PENDING ]; then echo "sed -i '' 's|^PENDING $p $own\$|OPEN $id $m $own|' $B" >> $BOARD
        else echo "printf '%s\n' 'OPEN $id $m $own' >> $B" >> $BOARD; fi
        grep -qxF "$p" $W/root-closure.txt && say "  !! $m is RED and in the ROOT closure"
        echo "$p $(blob $base $p)" >> $LAST; [ $v = BLOCKED ] && echo "$p" >> $BLK;;
      PENDING:GREEN)
        own=$(awk -v p="$p" '$1=="PENDING" && $2==p{print $3}' $B)
        echo "sed -i '' 's|^PENDING $p $own\$|GREEN $p $own (job $jid, ${base:0:10})|' $B" >> $BOARD;;
      OPEN:GREEN)
        id=$(id_of "$m")
        git show $M:research/$id.md > $W/research/$id.md 2>/dev/null || continue
        perl -0pi -e "s/^\*\*OPEN\.\*\*/**RESOLVED (${base:0:10}, trusted batched probe job $jid).** Previously OPEN./m" $W/research/$id.md
        EDITP="$EDITP research/$id.md"; RES="$RES $id"; sed -i '' "\|^$m\$|d" $UNK;;
      OPEN:RED|OPEN:BLOCKED)
        id=$(id_of "$m"); git show $M:research/$id.md > $W/research/$id.md 2>/dev/null || continue
        if [ -s $W/errs.tmp ]; then ERRS="$(cat $W/errs.tmp)" JID=$jid BASE=${base:0:10} perl -0pi -e 's/\*\*First errors \(verbatim[^\n]*\*\*\n\n```\n.*?\n```/**First errors (verbatim; refreshed from probe job $ENV{JID} on main $ENV{BASE}).**\n\n```\n$ENV{ERRS}\n```/s' $W/research/$id.md; fi
        echo "$id|$p|$deps" >> $W/pass.txt
        sed -i '' "\|^$p |d" $LAST; echo "$p $(blob $base $p)" >> $LAST; sed -i '' "\|^$m\$|d" $UNK
        [ $v = BLOCKED ] && echo "$p" >> $BLK;;
      OPEN:UNKNOWN*) echo "$m" >> $UNK;;
    esac
    [ -n "$st$v" ] && [ "$v" != GREEN -o -n "$st" ] && say "  $m ${st:-new} $v${deps:+ <- $deps}"
  done < $W/cand.txt
  # second pass: leaf-first requires edges, resolving ids created in this pass too
  { awk '$1=="OPEN"{print $3, $2}' $B | while read -r mm ii; do echo "$(m2p $mm) $ii"; done; awk -F'|' '{print $2, $1}' $W/pass.txt; } > $W/idmap.txt
  while IFS='|' read -r id p deps; do
    rids=""; for d in $deps; do x=$(awk -v d="$d" '$1==d{print $2; exit}' $W/idmap.txt); [ -n "$x" ] && [ "$x" != "$id" ] && rids="$rids $x"; done
    # shellcheck disable=SC2086
    set_requires $W/research/$id.md $rids
    case " $NEWP " in *" research/$id.md "*) ;; *) git show $M:research/$id.md | cmp -s - $W/research/$id.md || EDITP="$EDITP research/$id.md";; esac
  done < $W/pass.txt
  [ "${DRY:-0}" = 1 ] && { say "DRY: new=$NEWP edit=$EDITP res=$RES"; cat $BOARD >> $LOG; return 0; }
  if [ -n "$NEWP$EDITP" ]; then
    printf 'Cairn fix graph: verdicts from trusted batched probe job %s (main %s)\n\nNew fix nodes for red modules (leaf-first requires edges), RESOLVED for modules that built green on main, refreshed first errors and requires edges for modules still red.\n' "$jid" "${base:0:10}" > $GQ/msgs/fix-graph-lead-loop.txt
    # shellcheck disable=SC2086
    out=$(GQ_BASE=$(git rev-parse $M) GQ_BASE_PATHS="$EDITP" timeout 900 bash $GQ/gqland.sh fix-graph-lead $GQ/msgs/fix-graph-lead-loop.txt $NEWP $EDITP 2>&1 | grep -E 'LANDED|REFUSED|ABORT|error' | head -3)
    say "land: $out"
    echo "$out" | grep -q LANDED || return 1
    sha=$(echo "$out" | grep -oE 'LANDED [0-9a-f]+' | cut -d' ' -f2)
    for id in $RES; do echo "sed -i '' 's|^OPEN $id \(.*\)\$|RESOLVED $id \1 (${sha:0:10})|' $B" >> $BOARD; done
    [ -n "$RES" ] && { while read -r p; do sed -i '' "\|^$p |d" $LAST; done < $BLK; : > $BLK; }
  fi
  bash $BOARD; sort -u $UNK -o $UNK
  return 0
}

[ "${1:-}" = consume-one ] && { consume "$2"; exit $?; }
for tick in $(seq 1 72); do
  for r in $(ls -d $PQ/*/ 2>/dev/null | sed 's:/$::'); do
    [ -f $r/result ] || continue; grep -qxF "$r" $SEEN && continue
    [ -s $r/overlay.md5 ] && { echo "$r" >> $SEEN; continue; }
    [ $(stat -f %m $r/result) -lt $((T0 - 21600)) ] && { echo "$r" >> $SEEN; continue; }
    consume $r && echo "$r" >> $SEEN
  done
  inflight=$(for d in $(ls -d $PQ/*.fix-graph-lead 2>/dev/null); do [ -f $d/result ] || echo $d; done | head -1)
  now=$(date +%s)
  if [ -z "$inflight" ] && [ $((now - $(cat $LASTPROBE))) -ge 2700 ]; then
    : > $W/want.txt
    for m in $(awk '$1=="OPEN"{print $3}' $B); do p=$(m2p "$m"); old=$(awk -v p="$p" '$1==p{print $2}' $LAST | tail -1)
      { [ "$(blob $M $p)" != "${old:-x}" ] || grep -qxF "$m" $UNK; } && echo "$m" >> $W/want.txt; done
    awk '$1=="PENDING"{print $2}' $B | while read -r p; do p2m "$p"; done >> $W/want.txt
    if [ -s $W/want.txt ]; then echo $now > $LASTPROBE
      for g in 'BooneHigman\.Metabelian\.' 'Manuscript\.' '.'; do
        grep -E "^GroupApproximation\.$g" $W/want.txt > $W/want.g; grep -vxF -f $W/want.g $W/want.txt > $W/want.rest || true; mv $W/want.rest $W/want.txt
        [ -s $W/want.g ] || continue
        split -l 28 $W/want.g $W/want.part.
        for f in $W/want.part.*; do say "probe request ($(wc -l < $f | tr -d ' ')): $(tr '\n' ' ' < $f | cut -c1-200)"
          args=$(tr '\n' ' ' < $f); rm -f $f
          # shellcheck disable=SC2086
          nohup bash $GQ/gqprobe-lean.sh fix-graph-lead $args > $W/probe.$(date +%s).$RANDOM.out 2>&1 &
          sleep 3; done
      done
    fi
  fi
  sleep 600
done
say "loop3 finished"
