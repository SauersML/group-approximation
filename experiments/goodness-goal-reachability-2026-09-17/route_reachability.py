"""Reachability in the cairn route graph (edges: requires -> route -> target).

Usage: python3 route_reachability.py SRC[,BANNED...] ...
Prints a shortest path from SRC to the goal
torsion-free-sofic-exact-mf-radical-over-z avoiding the banned node or route
ids (a banned id also deletes every route that requires it), or UNREACHABLE.

Output on 2026-09-17 (swarm-0917-w14):
  every-hyperbolic-group-is-good                          : UNREACHABLE
  hyperbolic-finite-residual-is-torsion-free              : reachable, only via
      titz-witzel-flat-hitting-via-soficity-and-2d-vtf
  two-dimensional-cat0-hyperbolic-groups-virtually-torsion-free : same
  each of the last two, banning titz-witzel-flat-hitting-via-soficity-and-2d-vtf
                                                          : UNREACHABLE
"""
import os, re, sys
from collections import deque
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'research')
routes = {}
for f in os.listdir(D):
    if not f.endswith('.md'):
        continue
    t = open(os.path.join(D, f)).read()
    if not t.startswith('---'):
        continue
    fm = t.split('---', 2)[1]
    m = re.search(r'^target:\s*(\S+)', fm, re.M)
    if not m:
        continue
    req = []
    rm = re.search(r'^requires:\s*\n((?:[ \t]+- .*\n)+)', fm, re.M)
    if rm:
        req = re.findall(r'- (\S+)', rm.group(1))
    routes[f[:-3]] = (m.group(1), req)
goal = 'torsion-free-sofic-exact-mf-radical-over-z'
for line in sys.argv[1:]:
    parts = line.split(',')
    src, banned = parts[0], set(parts[1:])
    succ = {}
    for r, (t, req) in routes.items():
        if r in banned or any(b in req for b in banned):
            continue
        succ.setdefault(r, set()).add(t)
        for q in req:
            succ.setdefault(q, set()).add(r)
    prev = {src: None}
    Q = deque([src])
    while Q:
        x = Q.popleft()
        for y in sorted(succ.get(x, ())):
            if y in banned or y in prev:
                continue
            prev[y] = x
            Q.append(y)
    if goal in prev:
        p = [goal]
        while prev[p[-1]]:
            p.append(prev[p[-1]])
        print(src, 'ban', banned, ':', ' <- '.join(p))
    else:
        print(src, 'ban', banned, ': UNREACHABLE')
