set -u
RD=/projects/standard/hsiehph/sauer354/gk-steward
W=/projects/standard/hsiehph/sauer354/cc-gk-steward; cd "$W" || exit 1; PY=/usr/bin/python3.11
BASE=${1:-44fec21fb7dd7bd540c81959454070c9db22c1b3}
echo "clone HEAD=$(git rev-parse --short HEAD) base=${BASE:0:10} graph mtime=$(date -r .cairn/cache/graph.json +%H:%M)"
git diff --name-only --diff-filter=A "$BASE" HEAD -- research | grep -E '^research/[^/]+\.md$' | grep -v FRONTIER.md | sed 's#^research/##; s#\.md$##' > "$RD/out/added.txt"
nice -n 10 "$PY" - "$RD/out/added.txt" <<'PY'
import json, sys
g = json.load(open('.cairn/cache/graph.json'))
print('top keys:', list(g.keys())[:12])
n = g['nodes']
if isinstance(n, list):
    n = {d.get('id'): d for d in n}
k = 'gottschalk-surjunctivity-conjecture'
print('goal fields:', sorted(n[k].keys()))
print('goal reachable:', n[k].get('reachable'), 'status:', n[k].get('status'))
r = 'amenable-extensions-of-uqs-groups-proof'
if r in n: print('route sample:', json.dumps(n[r])[:500])
added = [l.strip() for l in open(sys.argv[1]) if l.strip()]
miss = [a for a in added if a not in n]
un = [a for a in added if a in n and not n[a].get('reachable')]
print('added', len(added), 'not-in-graph', len(miss), 'unreachable', len(un))
for a in miss[:10]: print('NOT-IN-GRAPH', a)
for a in un[:60]: print('UNREACHABLE', n[a].get('kind'), n[a].get('status'), a)
PY
echo ORPH-DONE
