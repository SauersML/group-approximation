#!/usr/bin/env python3
"""Stallings pullbacks for Linton's Z-stability and graph-of-cyclic-stabilisers inputs.

For subgroups P = <gens1>, Q = <gens2> of F(x,y), the core components of the pullback of their
pointed Stallings graphs correspond to the nontrivial intersections P^a cap Q^b over double
cosets P g Q (Stallings). The component containing the base pair (0,0), taken without trimming,
gives P cap Q itself. For each component this prints:
  rank = E - V + 1 of the core;
  a representative vertex (p, q), with tree words alpha (0 -> p in Gamma_P) and beta (0 -> q in Gamma_Q);
  generators: loop words at (p, q). As elements, alpha w alpha^-1 lies in P and beta w beta^-1 lies in Q.
Letters: x, X = x^-1, y, Y = y^-1.
Usage: lintonstab.py 'P gens comma-separated' 'Q gens comma-separated'
"""
import sys
from algext import stallings

INV = {'x': 'X', 'X': 'x', 'y': 'Y', 'Y': 'y'}

def reduce(w):
    out = []
    for ch in w:
        if out and out[-1] == INV[ch]:
            out.pop()
        else:
            out.append(ch)
    return ''.join(out)

def inv(w):
    return ''.join(INV[ch] for ch in reversed(w))

def adjacency(edges):
    adj = {}
    for (u, l, v) in edges:
        adj.setdefault(u, []).append((l, v))
        adj.setdefault(v, []).append((INV[l], u))
    return adj

def tree_words(nv, edges, root=0):
    adj, words, st = adjacency(edges), {root: ''}, [root]
    while st:
        u = st.pop()
        for l, v in sorted(adj.get(u, [])):
            if v not in words:
                words[v] = words[u] + l; st.append(v)
    return words

def pullback(E1, E2):
    """Product graph edges over matching letters (both orientations are recorded in E via label case)."""
    by1, by2 = {}, {}
    for (u, l, v) in E1:
        by1.setdefault(l, []).append((u, v))
    for (u, l, v) in E2:
        by2.setdefault(l, []).append((u, v))
    PE = set()
    for l in by1:
        for (u1, v1) in by1[l]:
            for (u2, v2) in by2.get(l, []):
                PE.add(((u1, u2), l, (v1, v2)))
    return PE

def components(PE, extra=()):
    verts = {u for (u, _, _) in PE} | {v for (_, _, v) in PE} | set(extra)
    adj = adjacency(PE)
    seen, comps = set(), []
    for s in sorted(verts):
        if s in seen:
            continue
        comp, st = {s}, [s]; seen.add(s)
        while st:
            u = st.pop()
            for _, v in adj.get(u, []):
                if v not in seen:
                    seen.add(v); comp.add(v); st.append(v)
        comps.append(comp)
    return comps

def core(comp, PE):
    V = set(comp)
    E = {e for e in PE if e[0] in V and e[2] in V}
    changed = True
    while changed:
        changed = False
        deg = {v: 0 for v in V}
        for (u, _, v) in E:
            deg[u] += 1; deg[v] += 1
        leaves = {v for v in V if deg[v] <= 1}
        if leaves:
            V -= leaves
            E = {e for e in E if e[0] in V and e[2] in V}
            changed = True
    return V, E

def loops(V, E, base):
    """Fundamental-cycle loop words at base for the graph (V, E)."""
    adj, words, tree, st = adjacency(E), {base: ''}, set(), [base]
    while st:
        u = st.pop()
        for l, v in sorted(adj.get(u, [])):
            if v not in words:
                words[v] = words[u] + l; st.append(v); tree.add(frozenset((u, v, l if l.islower() else INV[l])))
    gens = []
    used = set()
    for (u, l, v) in sorted(E):
        key = (u, l, v)
        tkey = frozenset((u, v, l))
        if tkey in tree and tkey not in used:
            used.add(tkey); continue
        gens.append(reduce(words[u] + l + inv(words[v])))
    return [g for g in gens if g]

def analyse(name, g1, g2):
    n1, E1 = stallings(g1)
    n2, E2 = stallings(g2)
    PE = pullback(E1, E2)
    t1, t2 = tree_words(n1, E1), tree_words(n2, E2)
    print('== %s: P=<%s> (V=%d,E=%d)  Q=<%s> (V=%d,E=%d)' % (name, ','.join(g1), n1, len(E1), ','.join(g2), n2, len(E2)))
    base = (0, 0)
    comps = components(PE, extra=[base])
    bc = next(c for c in comps if base in c)
    BE = {e for e in PE if e[0] in bc and e[2] in bc}
    bgens = loops(bc, BE, base)
    print('BASE P cap Q: rank=%d gens=%s' % (len(BE) - len(bc) + 1, bgens))
    for comp in comps:
        V, E = core(comp, PE)
        if not V:
            continue
        r = len(E) - len(V) + 1
        if r < 1:
            continue
        rep = min(V)
        gens = loops(V, E, rep)
        print('COMPONENT contains_base=%s rank=%d rep=%s alpha=%s beta=%s gens=%s' % (base in comp, r, rep, t1.get(rep[0], '?'), t2.get(rep[1], '?'), gens))
    print('SENTINEL_DONE', flush=True)

def main():
    g1 = sys.argv[1].split(','); g2 = sys.argv[2].split(',')
    analyse('pullback', g1, g2)

if __name__ == '__main__':
    main()
