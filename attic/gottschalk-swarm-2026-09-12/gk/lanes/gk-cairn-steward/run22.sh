set -u
RD=/projects/standard/hsiehph/sauer354/gk-steward
B0=${1:-54faf1cd6451e8e7ca533045374dd7a2b4070abe}
LOCK=$RD/check.lock
if [ -d "$LOCK" ] && [ -n "$(find "$LOCK" -maxdepth 0 -mmin +8)" ]; then rmdir "$LOCK" && echo "removed stale lock"; fi
bash $RD/gkcheck.sh
W=/projects/standard/hsiehph/sauer354/cc-gk-steward; cd "$W" || exit 1; PY=/usr/bin/python3.11
echo "--- requested statuses:"
for id in ternary-anti-central-summand-has-no-weakly-finite-image normal-surjunctive-decoder-memory-forces-surjectivity amenable-extensions-of-uqs-groups-are-surjunctive; do
  if [ ! -f "research/$id.md" ]; then echo "$id [NOT-IN-TREE]"; continue; fi
  CAIRN_ROOT="$W" nice -n 10 "$PY" tools/cairn.py why "$id" 2>&1 | grep -v 'graph warning' | grep -m1 -E '^\S+ \[' | cut -c1-120
done
echo "--- orphan and SCC audit (base ${B0:0:10}; old non-region SCCs omitted):"
bash $RD/orph2.sh "$B0" 2>&1 | grep -vE '^SCC old size [0-9]+ region 0 '
echo SENTINEL=done2
