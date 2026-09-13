set -u
RD=/projects/standard/hsiehph/sauer354/gk-steward
W=/projects/standard/hsiehph/sauer354/cc-gk-steward; cd "$W" || exit 1; PY=/usr/bin/python3.11
BASE=${1:-44fec21fb7dd7bd540c81959454070c9db22c1b3}
echo "clone HEAD=$(git rev-parse --short HEAD) base=${BASE:0:10} graph mtime=$(date -r .cairn/cache/graph.json +%H:%M)"
git diff --name-only --diff-filter=A "$BASE" HEAD -- research | grep -E '^research/[^/]+\.md$' | grep -v FRONTIER.md | sed 's#^research/##; s#\.md$##' > "$RD/out/added.txt"
nice -n 10 "$PY" - "$RD/out/added.txt" "$RD/region-ids.txt" <<'PY'
import json, sys
from collections import Counter
g = json.load(open('.cairn/cache/graph.json'))
n = g['nodes']
if isinstance(n, list): n = {d.get('id'): d for d in n}
added = set(l.strip() for l in open(sys.argv[1]) if l.strip())
region = set(l.strip() for l in open(sys.argv[2]) if l.strip())
ra = sorted(added & region)
print('region ids', len(region), 'in graph', sum(1 for r in region if r in n), '| added since base', len(added), 'region-added', len(ra))
un = [a for a in ra if a in n and not n[a].get('reachable')]
unc = [a for a in un if n[a].get('kind') == 'claim']
print('region-added unreachable: nodes', len(un), 'claims', len(unc), 'by status', dict(Counter(n[a].get('status') for a in unc)))
for a in unc[:45]: print('ORPHAN-CLAIM', n[a].get('status'), a)
r = 'amenable-extensions-of-uqs-groups-proof'
print('route meta keys:', sorted((n[r].get('meta') or {}).keys()) if r in n else 'n/a')
adj = {}; prov = {}
for k, d in n.items():
    if d.get('kind') != 'route': continue
    m = d.get('meta') or {}
    t = m.get('target'); req = m.get('requires') or []
    if isinstance(req, str): req = [req]
    if t not in n: continue
    for x in req:
        if x in n and n[x].get('kind') == 'claim':
            adj.setdefault(t, set()).add(x); prov.setdefault((t, x), set()).add(k)
idx = {}; low = {}; st = []; on = set(); sccs = []; c = 0
for s in sorted(adj):
    if s in idx: continue
    idx[s] = low[s] = c; c += 1; st.append(s); on.add(s); work = [(s, iter(sorted(adj.get(s, ()))))]
    while work:
        v, it = work[-1]; nxt = next(it, None)
        if nxt is None:
            work.pop()
            if work: low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == idx[v]:
                comp = []
                while True:
                    w = st.pop(); on.discard(w); comp.append(w)
                    if w == v: break
                if len(comp) > 1: sccs.append(comp)
        elif nxt not in idx:
            idx[nxt] = low[nxt] = c; c += 1; st.append(nxt); on.add(nxt); work.append((nxt, iter(sorted(adj.get(nxt, ())))))
        elif nxt in on:
            low[v] = min(low[v], idx[nxt])
print('nontrivial SCCs in claim graph:', len(sccs), 'sizes', sorted(len(x) for x in sccs))
for comp in sccs:
    cs = set(comp)
    newedge = any(rt in added for (t, x), rs in prov.items() if t in cs and x in cs for rt in rs)
    tag = 'NEW' if (cs & added or newedge) else 'old'
    print('SCC', tag, 'size', len(comp), 'region', len(cs & region), 'non-OPEN', sum(1 for x in comp if n[x].get('status') != 'OPEN'), ':', ' '.join(sorted(comp))[:420])
PY
echo ORPH2-DONE
