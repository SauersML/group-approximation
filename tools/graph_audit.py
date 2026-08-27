#!/usr/bin/env python3
"""Gate-blind audits over the compiled Cairn graph (.cairn/cache/graph.json).

`cairn check` validates references and duplicates; it does not read prose.
This script reports the traps recorded in the authoring notes:
  A. ESTABLISHED claims whose opening prose says open / conjecture.
  B. COMPLETE routes (requires: []) whose opening prose says dead / refuted.
  C. Claims carrying `invalidates:` that are not ESTABLISHED (their kills
     are inert until they are proved; listed for awareness).
  D. OPEN claims without an `## Attempts` section (legacy nodes).
  E. Backticked id-like tokens in bodies that name neither a node nor an
     artifact (stale references after renames).
  F. OPEN claims that an ESTABLISHED claim's `distinct_from` text calls its
     negation, with no `refuted_by:` recorded (unrecorded refutations).
  G. Single-prerequisite routes whose prerequisite STATEMENT (title+body,
     cairn.py's own TF-IDF geometry) is highly similar to the target's and
     not answered by `distinct_from` on either side: the "restatement
     dressed as reduction" trap.  `cairn check` compares titles only.
Run `bin/cairn check` first so the cache is fresh.  Read-only.
"""
import collections, glob, json, os, re, sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)
nodes = json.load(open('.cairn/cache/graph.json'))['nodes']
ids = set(nodes)
artifacts = {os.path.splitext(os.path.basename(p))[0] for p in glob.glob('research/artifacts/*.md')}

def split(path):
    s = open(path, encoding='utf-8', errors='replace').read()
    m = re.match(r'^---\n(.*?)\n---\n(.*)$', s, re.S)
    return (m.group(1), m.group(2)) if m else ('', s)

A, B, C, D = [], [], [], []
E = collections.Counter(); Eex = collections.defaultdict(set)
for nid, n in nodes.items():
    p = n.get('path')
    if not p or not os.path.exists(p):
        continue
    fm, body = split(p)
    head = body.strip()[:500]
    st = n.get('status', '')
    if n['kind'] == 'claim':
        if st == 'ESTABLISHED' and re.search(r'\bOPEN CLAIM\b|^Open claim|^OPEN in\b|^Conjecture[.:]|not yet proved|we do not prove', head, re.I | re.M):
            A.append(nid)
        if 'invalidates:' in fm and st != 'ESTABLISHED':
            C.append((nid, st))
        if st == 'OPEN' and '## Attempts' not in body:
            D.append(nid)
    else:
        if re.search(r'^requires:\s*\[\s*\]\s*$', fm, re.M) and st != 'INVALIDATED' and re.search(r'^\W*(dead|retired|refuted|invalidated)\b', head[:120], re.I):
            B.append((nid, st))
    for tok in re.findall(r'`([a-z0-9]+(?:-[a-z0-9]+){3,})`', body):
        if tok in ids or tok in artifacts or any(a.startswith(tok) for a in artifacts):
            continue
        if re.search(r'\d{4}-\d{2}-\d{2}', tok):
            continue
        E[tok] += 1; Eex[tok].add(nid)

F = []
for nid, n in nodes.items():
    if n['kind'] != 'claim' or n.get('status') != 'ESTABLISHED':
        continue
    fm, _ = split(n['path'])
    m = re.search(r'^distinct_from:\n((?:  .*\n)+)', fm + '\n', re.M)
    if not m:
        continue
    for line in m.group(1).splitlines():
        mm = re.match(r'  ([a-z0-9-]+):\s*(.*)', line)
        if not mm:
            continue
        key, txt = mm.groups()
        if key in nodes and nodes[key].get('status') == 'OPEN' and re.search(r'\bnegation\b|\bnegates\b', txt, re.I):
            if 'refuted_by' not in open(nodes[key]['path']).read():
                F.append((key, nid))

def show(title, items, limit=40):
    print(f'\n== {title}: {len(items)}')
    for x in items[:limit]:
        print('  ', x)
    if len(items) > limit:
        print(f'   ... and {len(items) - limit} more')

show('A. established claims with open/conjecture opening prose', A)
show('B. complete routes whose opening says dead/refuted', B)
show('C. invalidates: on non-established claims (inert kills)', C)
show('D. open claims without ## Attempts', D, 15)
show('F. open claims called "negation" by an established claim, no refuted_by', F)

# G. restatement-shaped single-prerequisite routes, scored on statements.
# cairn.py guards its CLI behind __main__, so importing it is side-effect free.
G = []
try:
    sys.path.insert(0, os.path.join(root, 'tools'))
    import cairn as _cairn
    _graph, _ = _cairn.compile_graph()
    _vecs = _cairn.semantic_vectors(_graph.claims)
    G_THRESHOLD = 0.14  # calibrated 2026-08-21: max over 431 single-prereq routes was 0.26, median 0.05
    for rid, r in _graph.routes.items():
        reqs = r.get_list('requires')
        tgt = r.meta.get('target')
        if len(reqs) != 1 or reqs[0] not in _graph.claims or tgt not in _graph.claims:
            continue
        a, b = _graph.claims[reqs[0]], _graph.claims[tgt]
        answered = (tgt in (a.meta.get('distinct_from') or {})
                    or reqs[0] in (b.meta.get('distinct_from') or {}))
        opposite = _cairn._negation_signature(a.title + ' ' + a.id) != _cairn._negation_signature(b.title + ' ' + b.id)
        if answered or opposite:
            continue
        sc = _cairn.cosine(_vecs.get(a.id, {}), _vecs.get(b.id, {}))
        if sc >= G_THRESHOLD:
            G.append((round(sc, 2), rid, reqs[0], tgt, nodes.get(rid, {}).get('status', '')))
    G.sort(reverse=True)
except Exception as ex:  # keep the other checks usable if cairn.py moves
    G = [('ERROR', repr(ex))]
show('G. single-prereq routes whose prerequisite statement ~ target statement (cosine>=0.14, unanswered; awareness, not error)', G, 40)
print(f'\n== E. dangling id-like tokens: {len(E)} distinct, {sum(E.values())} mentions')
for tok, c in E.most_common(25):
    print(f'   {c:3d}  {tok}   e.g. {sorted(Eex[tok])[0]}')
sys.exit(0)
