"""Fact F1: two distinct hull translates share at most 3 vertices.

A common vertex of T_K and g T_K (g not in K) has two different core types
(u, u'), u != u'.  A common subtree is a connected lift of a connected
subgraph of the off-diagonal product graph Core x Core minus diagonal, where
(u, u') -x-> (v, v') iff u -x-> v and u' -x-> v' in the core.  If every
component of that graph is a finite tree, a common subtree has at most as many
vertices as the largest component.
"""
from chains import STEP

V = [0, 1, 2]
nodes = [(u, w) for u in V for w in V if u != w]
adj = {n: set() for n in nodes}
edges = set()
for (u, w) in nodes:
    for x in 'aAbB':
        if (u, x) in STEP and (w, x) in STEP:
            m = (STEP[(u, x)], STEP[(w, x)])
            if m[0] != m[1]:
                adj[(u, w)].add(m)
                edges.add(frozenset([(u, w), m]))
seen, comps = set(), []
for n in nodes:
    if n in seen:
        continue
    comp, stack = set(), [n]
    while stack:
        z = stack.pop()
        if z in comp:
            continue
        comp.add(z)
        stack.extend(adj[z])
    seen |= comp
    ne = sum(1 for e in edges if set(e) <= comp)
    comps.append((len(comp), ne, sorted(comp)))
for c in comps:
    print('component vertices', c[0], 'edges', c[1], 'tree' if c[1] == c[0] - 1 else 'CYCLE', c[2])
print('max common subtree vertices', max(c[0] for c in comps))
