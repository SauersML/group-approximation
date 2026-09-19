#!/usr/bin/env bash
# fix-graph-lead maintenance loop v4 (main-only; gqprobe-lean.sh v4 batched probes). 10-min ticks, up to 12 h.
# Restart after a session restart:  bash $GQ/work/fix-graph-lead/loop4.sh   (Bash run_in_background)
# Test modes (DRY=1: no landing, board edits only printed to the log):  loop4.sh scan-one | consume-one <pq dir>
#
# Board lines (board/FIX-GRAPH.md), by shape:
#   node lines   OPEN|UNPROBED|RESOLVED <fix-id> <Module> <owner> [note]   (UNPROBED = repair landed, no trusted probe yet)
#   module lines PENDING|UNPROBED|GREEN <path> <owner> [note]              (no fix node; verdict pending or green)
#   SUPERSEDED a -> b
# Lanes write UNPROBED themselves; this loop keeps their notes unless a verdict changes the line.
#
# Each tick:
#  1. SCAN main since the last scan point for Lean landings (usually unprobed). A changed OPEN module -> UNPROBED plus a
#     "Repair landed, unprobed" line in its node. A changed GREEN module -> PENDING. A changed RESOLVED one -> recheck.
#     New unwired Lean off the board -> UNPROBED module line. Rooted modules are left to the root build gate.
#  2. CONSUME finished empty-overlay probe requests of any lane (verdicts per module from the remote per-request log):
#     RED (✖ or own error lines), BLOCKED (nearest red imports, which become `requires`), GREEN (rc 0, or a finished build
#     with no red module in the closure), else UNKNOWN. A verdict is dropped if another overlay in the same batch, or a
#     change on main since the probe's base, touches the module's import closure.
#     DEFERRED is never a verdict. A DEFERRED request whose batch ran (timeout or lost contact) is read for modules with
#     their own error lines only, and never for GREEN.
#  3. PROBE (unless $GQ/state/SLURM-BLOCKED exists; resume at once when it is gone), at most every 45 min with none of
#     this lane's requests in flight: node modules changed since last seen red or UNKNOWN, all module lines, and
#     rechecks. Grouped requests, empty overlay.
set -uo pipefail
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
W=$GQ/work/fix-graph-lead; B=$GQ/board/FIX-GRAPH.md; PQ=$GQ/state/pq; REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi; PHOME=/projects/standard/hsiehph/sauer354; M=refs/remotes/origin/main
LOG=$W/loop.log; SEEN=$W/seen-results3.txt; LAST=$W/last-red-blob.tsv; UNK=$W/unknown.txt; BLK=$W/blocked.txt
RECHECK=$W/recheck.txt; LASTPROBE=$W/last-probe-epoch; SCAN=$W/scan-sha; T0=$(date +%s)
touch $SEEN $LAST $UNK $BLK $RECHECK; : > $W/overlay.files; [ -f $LASTPROBE ] || echo 0 > $LASTPROBE
cd $REPO || exit 2
say() { echo "$(date '+%F %T') $*" >> $LOG; }
m2p() { echo "$(echo "$1" | tr . /).lean"; }
p2m() { echo "${1%.lean}" | tr / .; }
msi() { "$MSI" "$@" < /dev/null 2>&1 | tr -d '\r'; }
blob() { git rev-parse -q --verify "$1:$2" 2>/dev/null || echo NONE; }

# ---- board access (by line shape)
status_of() { # $1 path -> sets ST (OPEN|PENDING|RESOLVED|GREEN|"", UNPROBED mapped by line shape) and RAWST (raw word)
  local p=$1 m; m=$(p2m "$1")
  RAWST=$(awk -v p="$p" -v m="$m" '
    ($1=="OPEN"||$1=="UNPROBED"||$1=="RESOLVED") && $2 ~ /^fix-/ && $3==m {print $1; exit}
    ($1=="PENDING"||$1=="UNPROBED"||$1=="GREEN") && $2 !~ /^fix-/ { for(i=2;i<=NF;i++) if($i==p||$i==m){print $1 "-mod"; exit} }' $B)
  case "$RAWST" in OPEN|UNPROBED) ST=OPEN;; RESOLVED) ST=RESOLVED;; PENDING-mod|UNPROBED-mod) ST=PENDING;; GREEN-mod) ST=GREEN;; *) ST="";; esac
}
id_of() { awk -v m="$1" '($1=="OPEN"||$1=="UNPROBED"||$1=="RESOLVED") && $2 ~ /^fix-/ && $3==m{print $2; exit}' $B; }
owner_on_board() { # $1 path -> owner field of its node or module line
  local m; m=$(p2m "$1"); awk -v p="$1" -v m="$m" '($2 ~ /^fix-/ && $3==m){print $4; exit} ($2 !~ /^fix-/){for(i=2;i<NF;i++) if($i==p||$i==m){print $(i+1); exit}}' $B
}
KEYMATCH='function hit(  i, km) { if (k ~ /^fix-/) return $2==k; km=k; sub(/\.lean$/,"",km); gsub(/\//,".",km); for(i=2;i<=NF;i++) if($i==k||$i==km) return 1; return 0 }'
board_set() { # $1 key (fix id or path) $2 new line: replaces the first live line with that key, or appends
  awk -v k="$1" -v nl="$2" "$KEYMATCH"' BEGIN{split(nl,w," ")} hit() && ($1=="OPEN"||$1=="UNPROBED"||$1=="PENDING"||$1=="GREEN"||$1=="RESOLVED"){ if(!done){print nl; done=1} else {$1=w[1]; print}; next} {print} END{if(!done) print nl}' $B > $B.tmp.$$ && mv $B.tmp.$$ $B
}
board_note() { # $1 key $2 note: append " (note)" to that line, replacing an earlier note of the same kind ($3 = kind regex)
  awk -v k="$1" -v nt="$2" -v kr="$3" "$KEYMATCH"' hit() && !done && $1!="SUPERSEDED" { if (kr!="") gsub(" \\(" kr "[^)]*\\)", ""); print $0 " (" nt ")"; done=1; next } {print}' $B > $B.tmp.$$ && mv $B.tmp.$$ $B
}

# ---- import graph
edges() { local f=$W/edges.$1
  [ -s $f ] || git grep '^import GroupApproximation' $1 -- 'GroupApproximation/*.lean' | sed -E "s|^[^:]+:([^:]+):import (.*)$|\1 \2|" \
    | awk '{gsub(/\./,"/",$2); print $1, $2".lean"}' > $f
  echo $f; }
closure() { awk -v s="$2" '{adj[$1]=adj[$1]" "$2} END{q[1]=s; seen[s]=1; h=1; t=1; while(h<=t){f=q[h++]; n=split(adj[f],a," "); for(i=1;i<=n;i++) if(!(a[i] in seen)){seen[a[i]]=1; q[++t]=a[i]}} for(k in seen) print k}' $1; }
nearest_red() { awk -v s="$2" 'FILENAME==ARGV[1]{red[$1]=1; next} {adj[$1]=adj[$1]" "$2} END{q[1]=s; seen[s]=1; h=1; t=1; while(h<=t){f=q[h++]; n=split(adj[f],a," "); for(i=1;i<=n;i++) if(!(a[i] in seen)){seen[a[i]]=1; if(a[i] in red) print a[i]; else q[++t]=a[i]}}}' $3 $1; }
rootclo() { local e; e=$(edges $1)
  git show $1:GroupApproximation.lean | awk '/^import GroupApproximation/{print $2}' | while read -r x; do m2p "$x"; done > $W/rootstarts.tmp
  awk 'FILENAME==ARGV[1]{q[++t]=$1; seen[$1]=1; next} {adj[$1]=adj[$1]" "$2} END{h=1; while(h<=t){f=q[h++]; n=split(adj[f],a," "); for(i=1;i<=n;i++) if(!(a[i] in seen)){seen[a[i]]=1; q[++t]=a[i]}} for(k in seen) print k}' $W/rootstarts.tmp $e; }

# ---- nodes
owner() { case "$1" in
    GroupApproximation/BooneHigman/Metabelian/*) echo bh-pal-wire; return;;
    GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/*|GroupApproximation/Manuscript/SimpleKazhdanSofic/SkRows/*) echo ms-green-sk; return;;
    GroupApproximation/Manuscript/NonMF/*) echo ms-green-nm; return;;
  esac
  local d o=""; d=$(dirname "$1")
  while [ -z "$o" ] && [ "$d" != GroupApproximation ] && [ "$d" != . ]; do
    o=$(awk -F'\t' -v d="$d" '$2=="lean"{x=$4; sub(/\/[^\/]*$/,"",x); if(x==d) print $3}' $GQ/state/unlanded2.tsv | sort | uniq -c | sort -rn | awk 'NR==1{print $2}')
    d=$(dirname "$d"); done
  echo "${o:-unowned}"; }
slug_id() { local s=${1#GroupApproximation/} id n=2 c; s=${s%.lean}
  s=$(echo "$s" | sed -e 's|^BooneHigman/Metabelian/|bhmet/|' -e 's|^Manuscript/SimpleKazhdanSofic/|sk/|' -e 's|^Manuscript/NonMF/|nm/|')
  id="fix-$(echo "$s" | sed -E 's/([a-z0-9])([A-Z])/\1-\2/g; s/([A-Z])([A-Z][a-z])/\1-\2/g' | tr 'A-Z/_' 'a-z--' | tr -s '-' | cut -c1-60 | sed 's/-$//')"; c=$id
  while git cat-file -e "$M:research/$c.md" 2>/dev/null && ! git show "$M:research/$c.md" | grep -qF "\`$1\`"; do c="$id-$n"; n=$((n+1)); done
  echo "$c"; }
set_requires() { local f=$1; shift; local R=""; for x in "$@"; do R="$R  - $x\n"; done
  REQ="$R" perl -0pi -e 's/\A(---\n.*?)\nrequires:\n(?:  - [^\n]*\n)*/$1\n/s; s/\A(---\n.*?\n)---\n/$1 . ($ENV{REQ} ne "" ? "requires:\n$ENV{REQ}" : "") . "---\n"/se' $f; }
drop_repair_line() { perl -0pi -e 's/\n\*\*Repair landed, unprobed\.\*\*[^\n]*\n/\n/' $1; }
new_node() { # $1 path $2 owner $3 jid $4 base $5 errsfile -> id
  local p=$1 own=$2 jid=$3 base=$4 ef=$5 m id short; m=$(p2m "$p"); id=$(slug_id "$p")
  short=$(head -1 $ef | sed -E 's/^error: [^ ]+: //' | tr -d '"`' | cut -c1-70); [ -z "$short" ] && short="fails through red imports"
  { echo "---"; echo "rg: 2"; echo "id: $id"; echo "kind: route"; echo "title: \"Fix $m: $short\""; echo "---"; echo
    echo "**OPEN.** Lean module \`$p\` is red on main at ${base:0:10} (trusted batched probe, Slurm job $jid, empty overlay). It is not in the root closure."
    echo "It is part of the Cairn fix graph (index \`board/FIX-GRAPH.md\` in the swarm workspace). Owner: $own."
    echo; echo "**First errors (verbatim).**"; echo; echo '```'
    if [ -s $ef ]; then cat $ef; else echo "(none in this file: it fails only because red imports fail; see requires)"; fi; echo '```'
    echo; echo "**What it needs.** Make \`$m\` compile under the repository settings without changing any statement."
    echo "When \`requires\` lists nodes, those are its nearest red imports. Fix them first."
    echo; echo "**Resolution.** When a trusted probe builds it green, change the status line above to \`**RESOLVED (<green commit>).**\`."
  } > $W/research/$id.md
  echo "$id"; }
land() { # $1 msg file, rest: paths; edited existing paths are GQ_BASE-checked
  local msg=$1; shift; local edits=""; for x in "$@"; do git cat-file -e "$M:$x" 2>/dev/null && edits="$edits $x"; done
  GQ_BASE=$(git rev-parse $M) GQ_BASE_PATHS="$edits" timeout 900 bash $GQ/gqland.sh fix-graph-lead "$msg" "$@" 2>&1 | grep -E 'LANDED|REFUSED|ABORT|error' | head -3; }

# ---- 1. scan landings
scan_landings() {
  local old new EDITS="" c sub st own id m
  new=$(git rev-parse $M); [ -s $SCAN ] || echo 3c8b417428 > $SCAN; old=$(git rev-parse "$(cat $SCAN)")
  [ "$old" = "$new" ] && return 0
  git merge-base --is-ancestor $old $new || { say "scan: $old not an ancestor of main; scan restarts at main"; echo $new > $SCAN; return 0; }
  git diff --name-status $old $new -- 'GroupApproximation/*.lean' | awk '$1 ~ /^[AMD]$/' > $W/scan.tmp
  [ -s $W/scan.tmp ] || { echo $new > $SCAN; return 0; }
  rootclo $new > $W/root-closure.txt; : > $W/scan-board.sh
  while read -r s p; do
    m=$(p2m "$p"); c=$(git log -1 --format='%h' $old..$new -- "$p"); sub=$(git log -1 --format='%s' $old..$new -- "$p" | tr -d "'\"|" | cut -c1-90)
    status_of "$p"; st=$ST
    case "$st:$s" in
      OPEN:D) say "scan: node module $m deleted at $c"; echo "board_note $(id_of $m) 'module deleted at $c' 'module deleted'" >> $W/scan-board.sh;;
      OPEN:*) id=$(id_of "$m"); own=$(owner_on_board "$p")
        git show $M:research/$id.md > $W/research/$id.md 2>/dev/null || continue
        drop_repair_line $W/research/$id.md
        perl -pi -e 's/^Source changed on main since that build: no\.$/Source changed on main since that build: yes./' $W/research/$id.md
        LINE="**Repair landed, unprobed.** $c: $sub. Stays OPEN until a trusted probe builds it green." perl -0pi -e 's/(\n\n\*\*First errors)/\n\n$ENV{LINE}$1/' $W/research/$id.md
        git show $M:research/$id.md | cmp -s - $W/research/$id.md || EDITS="$EDITS research/$id.md"
        if [ "$RAWST" = OPEN ]; then echo "board_set $id 'UNPROBED $id $m $own -- repair landed $c (unprobed)'" >> $W/scan-board.sh
        else echo "board_note $id 'repair landed $c' 'repair landed'" >> $W/scan-board.sh; fi
        echo "$m" >> $RECHECK; say "scan: repair of $m landed at $c, unprobed";;
      GREEN:D|PENDING:D) say "scan: module $m deleted at $c"; echo "board_note $p 'deleted at $c' 'deleted'" >> $W/scan-board.sh;;
      GREEN:*) own=$(owner_on_board "$p"); echo "board_set $p 'UNPROBED $p $own (changed at $c after green)'" >> $W/scan-board.sh; say "scan: GREEN $m changed at $c";;
      RESOLVED:*) id=$(id_of "$m"); echo "board_note $id 'changed at $c, unverified' 'changed at'" >> $W/scan-board.sh; echo "$m" >> $RECHECK
        say "scan: RESOLVED $m changed at $c; recheck";;
      PENDING:*) [ "$RAWST" = UNPROBED-mod ] || echo "board_note $p 'landed $c' 'landed'" >> $W/scan-board.sh;;
      :D) ;;
      :*) grep -qxF "$p" $W/root-closure.txt && { say "scan: rooted $m changed at $c (root build gate covers it)"; continue; }
        own=$(owner "$p"); echo "board_set $p 'UNPROBED $p $own (landed $c, unprobed; not root-wired)'" >> $W/scan-board.sh
        say "scan: new unwired Lean $m at $c -> UNPROBED ($own)";;
    esac
  done < $W/scan.tmp
  if [ "${DRY:-0}" = 1 ]; then say "DRY scan: edits=$EDITS"; cat $W/scan-board.sh >> $LOG; return 0; fi
  if [ -n "$EDITS" ]; then
    printf 'Cairn fix graph: record the unprobed repairs landed on main up to %s\n\nEvery OPEN fix node whose module changed on main since the last scan now names the landing commit. It stays OPEN until a trusted probe builds it green.\n' "${new:0:10}" > $GQ/msgs/fix-graph-lead-scan.txt
    # shellcheck disable=SC2086
    out=$(land $GQ/msgs/fix-graph-lead-scan.txt $EDITS); say "scan land: $out"; echo "$out" | grep -q LANDED || return 1
  fi
  . $W/scan-board.sh; echo $new > $SCAN; sort -u $RECHECK -o $RECHECK; return 0
}

# ---- 2. consume verdicts
consume() {
  local r=$1 V L jid base n rc bat RL RAW E OTHER RS complete partial=no NEWP="" EDITP="" RES="" st v deps own id m p
  V=$(head -1 $r/result); L=$(echo "$V" | grep -oE 'log=[^ ]+' | cut -d= -f2); jid=$(echo "$V" | grep -oE 'job=[0-9]+' | cut -d= -f2)
  if [ -z "$jid" ] && [ -n "$L" ] && [ -f "$L" ]; then jid=$(sed -n '1s/.*batch job \([0-9]*\) (.*/\1/p' "$L"); partial=yes; fi
  if [ -z "$jid" ] || [ ! -f "$L" ]; then say "skip $(basename $r): $(echo "$V" | cut -c1-80)"; return 0; fi
  base=$(sed -n '1s/^base \([0-9a-f]*\);.*/\1/p' "$L"); n=$(sed -n '1s/.*batch job [0-9]* (\([0-9]*\) of.*/\1/p' "$L")
  rc=$(sed -n '1s/.*; rc \([0-9a-z]*\)$/\1/p' "$L")
  bat=$(msi "sacct -j $jid -X -n -P -o SubmitLine | head -1" | grep -oE 'batch-b[0-9]+' | head -1)
  if [ -z "$bat" ] || [ -z "$n" ] || [ -z "$base" ]; then say "retry later $(basename $r): cannot locate remote log"; return 1; fi
  RL=$PHOME/gq-slurm/$bat-$n.log
  RAW=$(msi "grep -aE '✖ |^error: GroupApproximation/|build failed|Build completed' $RL 2>/dev/null | cut -c1-240 | head -8000; echo SENTINEL")
  echo "$RAW" | grep -q SENTINEL || { say "retry later $(basename $r): remote log unreadable"; return 1; }
  E=$(edges $base); RS=$W/red.$jid.$n
  { echo "$RAW" | sed -nE 's/^✖ \[[0-9]+\/[0-9]+\] [A-Za-z]+ ([A-Za-z0-9_.]+).*/\1/p' | while read -r x; do m2p "$x"; done
    echo "$RAW" | sed -nE 's/^error: (GroupApproximation\/[^:]+\.lean):.*/\1/p'; } | sort -u > $RS
  complete=no; { [ "$rc" = 0 ] || echo "$RAW" | grep -qE 'build failed|Build completed'; } && complete=yes
  if [ $partial = yes ]; then complete=no; echo "$RAW" | sed -nE 's/^error: (GroupApproximation\/[^:]+\.lean):.*/\1/p' | sort -u > $RS; fi
  git diff --name-only $base $M -- GroupApproximation/ > $W/changed.$jid.$n
  OTHER=$W/other.$jid.$n
  for x in $PQ/*/result; do d=$(dirname $x); [ "$d" = "$r" ] && continue; l=$(head -1 $x | grep -oE 'log=[^ ]+' | cut -d= -f2)
    [ -n "$l" ] && [ -f "$l" ] && head -1 "$l" | grep -q "batch job $jid (" && awk '{print $2}' $d/overlay.md5; done | sort -u > $OTHER
  say "consume $(basename $r) job $jid ($bat-$n) base ${base:0:10} rc ${rc:-?} complete=$complete partial=$partial red=$(wc -l < $RS | tr -d ' ') other-overlays=$(wc -l < $OTHER | tr -d ' ')"
  : > $W/board-edits.sh; : > $W/pass.txt
  { cat $RS; for t in $(cat $r/targets); do m2p "$t"; done; } | awk '!s[$0]++' > $W/cand.txt
  while read -r p; do
    m=$(p2m "$p"); v=UNKNOWN
    closure $E "$p" > $W/clo.tmp
    deps=$(nearest_red $E "$p" $RS | sort -u | tr '\n' ' ')
    echo "$RAW" | grep -F "error: $p:" | head -4 > $W/errs.tmp
    if [ -s $OTHER ] && grep -qxF -f $OTHER $W/clo.tmp; then v=UNKNOWN_BATCH
    elif [ -s $W/changed.$jid.$n ] && grep -qxF -f $W/changed.$jid.$n $W/clo.tmp; then v=UNKNOWN_STALE
    elif grep -qxF "$p" $RS; then v=RED; [ ! -s $W/errs.tmp ] && [ -n "$deps" ] && v=BLOCKED
    elif [ -n "$deps" ]; then v=BLOCKED
    elif [ $complete = yes ]; then v=GREEN; fi
    status_of "$p"; st=$ST; own=$(owner_on_board "$p"); [ -n "$own" ] || own=$(owner "$p")
    case "$st:$v" in
      PENDING:RED|PENDING:BLOCKED|:RED)
        id=$(new_node "$p" "$own" "$jid" "$base" $W/errs.tmp); NEWP="$NEWP research/$id.md"; echo "$id|$p|$deps" >> $W/pass.txt
        echo "board_set $p 'OPEN $id $m $own'" >> $W/board-edits.sh
        grep -qxF "$p" $W/root-closure.txt 2>/dev/null && say "  !! $m is RED and in the ROOT closure"
        echo "$p $(blob $base $p)" >> $LAST; [ $v = BLOCKED ] && echo "$p" >> $BLK;;
      PENDING:GREEN) echo "board_set $p 'GREEN $p $own (job $jid, ${base:0:10})'" >> $W/board-edits.sh;;
      OPEN:GREEN) id=$(id_of "$m"); git show $M:research/$id.md > $W/research/$id.md 2>/dev/null || continue
        drop_repair_line $W/research/$id.md
        perl -0pi -e "s/^\*\*OPEN\.\*\*/**RESOLVED (${base:0:10}, trusted batched probe job $jid).** Previously OPEN./m" $W/research/$id.md
        EDITP="$EDITP research/$id.md"; RES="$RES $id|$m|$own"; sed -i '' "\|^$m\$|d" $UNK $RECHECK;;
      OPEN:RED|OPEN:BLOCKED) id=$(id_of "$m"); git show $M:research/$id.md > $W/research/$id.md 2>/dev/null || continue
        drop_repair_line $W/research/$id.md
        if [ -s $W/errs.tmp ]; then ERRS="$(cat $W/errs.tmp)" JID=$jid BASE=${base:0:10} perl -0pi -e 's/\*\*First errors \(verbatim[^\n]*\*\*\n\n```\n.*?\n```/**First errors (verbatim; from probe job $ENV{JID} on main $ENV{BASE}).**\n\n```\n$ENV{ERRS}\n```/s' $W/research/$id.md; fi
        echo "$id|$p|$deps" >> $W/pass.txt
        [ "$RAWST" = UNPROBED ] && echo "board_set $id 'OPEN $id $m $own (still $v after repair; job $jid)'" >> $W/board-edits.sh
        sed -i '' "\|^$p |d" $LAST; echo "$p $(blob $base $p)" >> $LAST; sed -i '' "\|^$m\$|d" $UNK $RECHECK
        [ $v = BLOCKED ] && echo "$p" >> $BLK;;
      OPEN:UNKNOWN*) echo "$m" >> $UNK;;
      RESOLVED:RED|RESOLVED:BLOCKED) say "  !! RESOLVED $m is $v again (job $jid)"; echo "board_note $(id_of $m) 'RED AGAIN job $jid' 'RED AGAIN'" >> $W/board-edits.sh;;
    esac
    { [ -n "$st" ] || [ "$v" = RED ]; } && say "  $m ${st:-new} $v${deps:+ <- $deps}"
  done < $W/cand.txt
  # leaf-first requires edges (ids created in this pass included)
  { awk '($1=="OPEN"||$1=="UNPROBED") && $2 ~ /^fix-/{print $3, $2}' $B | while read -r mm ii; do echo "$(m2p $mm) $ii"; done; awk -F'|' '{print $2, $1}' $W/pass.txt; } > $W/idmap.txt
  while IFS='|' read -r id p deps; do
    rids=""; for d in $deps; do x=$(awk -v d="$d" '$1==d{print $2; exit}' $W/idmap.txt); [ -n "$x" ] && [ "$x" != "$id" ] && rids="$rids $x"; done
    # shellcheck disable=SC2086
    set_requires $W/research/$id.md $rids
    case " $NEWP " in *" research/$id.md "*) ;; *) git show $M:research/$id.md | cmp -s - $W/research/$id.md || EDITP="$EDITP research/$id.md";; esac
  done < $W/pass.txt
  if [ "${DRY:-0}" = 1 ]; then say "DRY: new=$NEWP edit=$EDITP res=$RES"; cat $W/board-edits.sh >> $LOG; return 0; fi
  if [ -n "$NEWP$EDITP" ]; then
    printf 'Cairn fix graph: verdicts from trusted batched probe job %s (main %s)\n\nNew fix nodes for red modules (leaf-first requires edges), RESOLVED where the module built green on main, and refreshed first errors and requires edges where it is still red.\n' "$jid" "${base:0:10}" > $GQ/msgs/fix-graph-lead-loop.txt
    # shellcheck disable=SC2086
    out=$(land $GQ/msgs/fix-graph-lead-loop.txt $NEWP $EDITP); say "land: $out"; echo "$out" | grep -q LANDED || return 1
    sha=$(echo "$out" | grep -oE 'LANDED [0-9a-f]+' | cut -d' ' -f2)
    for x in $RES; do IFS='|' read -r id mm oo <<< "$x"; echo "board_set $id 'RESOLVED $id $mm $oo (${sha:0:10})'" >> $W/board-edits.sh; done
    [ -n "$RES" ] && { while read -r q; do sed -i '' "\|^$q |d" $LAST; done < $BLK; : > $BLK; }
  fi
  . $W/board-edits.sh; sort -u $UNK -o $UNK; return 0
}

[ "${1:-}" = scan-one ] && { scan_landings; exit $?; }
[ "${1:-}" = consume-one ] && { consume "$2"; exit $?; }
blocked=no
for tick in $(seq 1 72); do
  scan_landings
  for r in $(ls -d $PQ/*/ 2>/dev/null | sed 's:/$::'); do
    [ -f $r/result ] || continue; grep -qxF "$r" $SEEN && continue
    [ -s $r/overlay.md5 ] && { echo "$r" >> $SEEN; continue; }
    [ $(stat -f %m $r/result) -lt $((T0 - 21600)) ] && { echo "$r" >> $SEEN; continue; }
    consume $r && echo "$r" >> $SEEN
  done
  if [ -e $GQ/state/SLURM-BLOCKED ]; then
    [ $blocked = yes ] || say "SLURM-BLOCKED present: not submitting probes (still reading verdicts and landings)"; blocked=yes
    sleep 600; continue
  elif [ $blocked = yes ]; then say "SLURM-BLOCKED gone: resuming probes now"; blocked=no; echo 0 > $LASTPROBE; fi
  inflight=$(for d in $(ls -d $PQ/*.fix-graph-lead 2>/dev/null); do [ -f $d/result ] || echo $d; done | head -1)
  now=$(date +%s)
  if [ -z "$inflight" ] && [ $((now - $(cat $LASTPROBE))) -ge 2700 ]; then
    : > $W/want.txt
    for m in $(awk '($1=="OPEN"||$1=="UNPROBED") && $2 ~ /^fix-/{print $3}' $B); do p=$(m2p "$m"); old=$(awk -v p="$p" '$1==p{print $2}' $LAST | tail -1)
      { [ "$(blob $M $p)" != "${old:-x}" ] || grep -qxF "$m" $UNK; } && echo "$m" >> $W/want.txt; done
    awk '($1=="PENDING"||$1=="UNPROBED") && $2 ~ /^GroupApproximation\//{print $2}' $B | while read -r p; do git cat-file -e "$M:$p" 2>/dev/null && p2m "$p"; done >> $W/want.txt
    cat $RECHECK >> $W/want.txt; sort -u $W/want.txt -o $W/want.txt
    if [ -s $W/want.txt ]; then echo $now > $LASTPROBE
      for g in 'BooneHigman\.Metabelian\.' 'Manuscript\.' '.'; do
        grep -E "^GroupApproximation\.$g" $W/want.txt > $W/want.g; grep -vxF -f $W/want.g $W/want.txt > $W/want.rest || true; mv $W/want.rest $W/want.txt
        [ -s $W/want.g ] || continue
        split -l 28 $W/want.g $W/want.part.
        for f in $W/want.part.*; do args=$(tr '\n' ' ' < $f); rm -f $f
          say "probe request ($(echo $args | wc -w | tr -d ' ')): $(echo "$args" | cut -c1-200)"
          # shellcheck disable=SC2086
          nohup bash $GQ/gqprobe-lean.sh fix-graph-lead $args > $W/probe.$(date +%s).$RANDOM.out 2>&1 &
          sleep 3; done
      done
    fi
  fi
  sleep 600
done
say "loop4 finished"
