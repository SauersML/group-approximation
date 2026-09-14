#!/usr/bin/env python3
"""Tietze closure of a LOT presentation.

If a generator x occurs exactly once in a relator r, eliminating x (solve r for x, substitute
into the other relators, delete x and r) is a Tietze transformation realised by Andrews--Curtis
moves followed by a collapse, hence a 3-deformation.  So every state reachable by such
eliminations has the same homotopy type as K(Gamma), with deficiency 1, H_1 = Z and relators of
total exponent 0.  lot2.py's label presentations are the special states where exactly the
non-label vertices are eliminated.  Each state is tested with Barreto--Minian Thms 2.5 / 2.18 and
the Barmak--Minian I-test.
"""
from lot import rel, test_itest
from lot2 import cyc_reduce, inv, test_bm25, test_bm218

def cmin(w):
    best, L = None, len(w)
    for s in range(max(L, 1)):
        for ww in (w[s:] + w[:s], inv(w[s:] + w[:s])):
            t = tuple(ww)
            if best is None or t < best: best = t
    return best

def eliminate(gens, rels, k, x):
    r = rels[k]
    pos = [p for p, (g, e) in enumerate(r) if g == x]
    if len(pos) != 1: return None
    p = pos[0]; e = r[p][1]
    rot = r[p + 1:] + r[:p]            # r ~ x^e rot, so x^e = rot^-1
    W = inv(rot) if e == 1 else rot
    new = []
    for j, s in enumerate(rels):
        if j == k: continue
        out = []
        for (g, ee) in s:
            if g == x: out.extend(W if ee == 1 else inv(W))
            else: out.append((g, ee))
        new.append(cyc_reduce(out))
    return tuple(v for v in gens if v != x), new

def relabel(gens, rels):
    idx = {v: r for r, v in enumerate(gens)}
    return len(gens), [[(idx[g], e) for (g, e) in r] for r in rels]

def tietze_closure_test(n, E, max_states=20000, max_len=400):
    start = (tuple(range(n)), [rel(e) for e in E])
    seen, queue, states = set(), [start], 0
    while queue and states < max_states:
        gens, rels = queue.pop(0)
        key = (gens, tuple(sorted(cmin(r) for r in rels)))
        if key in seen: continue
        seen.add(key); states += 1
        if any(not r for r in rels):
            return 'EMPTY_RELATOR', {'gens': gens, 'rels': rels}   # would contradict asphericity
        g, R = relabel(gens, rels)
        for name, f in (('T-bm25', test_bm25), ('T-bm218', test_bm218)):
            c = f(g, R)
            if c: c.update(gens=list(gens), rels=R); return name, c
        c = test_itest(g, None, rels=R, vs=[[1] * g, [-1] * g])
        if c: c.update(gens=list(gens), rels=R); return 'T-itest', c
        for k in range(len(rels)):
            for x in {v for (v, _) in rels[k]}:
                nxt = eliminate(gens, rels, k, x)
                if nxt and all(len(r) <= max_len for r in nxt[1]): queue.append(nxt)
    return None, {'states': states}
