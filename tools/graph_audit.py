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
print(f'\n== E. dangling id-like tokens: {len(E)} distinct, {sum(E.values())} mentions')
for tok, c in E.most_common(25):
    print(f'   {c:3d}  {tok}   e.g. {sorted(Eex[tok])[0]}')
sys.exit(0)
