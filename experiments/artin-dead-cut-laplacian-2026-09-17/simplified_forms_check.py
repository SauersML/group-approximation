"""Companion check for artin-sigma1-equals-dead-cut-laplacian-surjectivity.

This check uses the *simplified* relation generators of the claim:
  (D) dead edge {p,q}:            g = S_k(pq)(p-1)
  (V) {w,x}, w dead, x living:    g = S_k'(wx)(w-1)     between [x] and [u(w)]
  (W) {w,x}, both dead:           g = (dr_wx/dw)(w-1)    between [u(w)] and [u(x)]
They generate the same left ideals as the unsimplified generators in
dead_cut_laplacian_check.py. The reason is the fundamental formula
sum_x (dr/dx)(x-1) = 0 together with the units (1-x) and S_k'(wx).

The check recomputes dim coker L_chi with them on the same random instances and
compares it with dim H_1 of the full complex.
"""
import random
import numpy as np
import dead_cut_laplacian_check as M


def reduced_simplified(V, E, chi, R):
    n = R.n
    liv = [x for x in V if chi[x] != 0]
    dead = [x for x in V if chi[x] == 0]
    comp = {x: x for x in liv}

    def find(x):
        while comp[x] != x:
            x = comp[x]
        return x

    def isdead(a, b, l):
        return l % 2 == 0 and l >= 4 and chi[a] + chi[b] == 0

    for (a, b), l in E.items():
        if chi[a] and chi[b] and not isdead(a, b, l):
            comp[find(a)] = find(b)
    choice = {}
    for w in dead:
        opts = [(x, e) for (e, l) in E.items() for x in e
                if w in e and x != w and chi[x] != 0]
        if not opts:
            return None
        choice[w] = opts[0]
    blocks = sorted({find(x) for x in liv})
    pos = {c: i for i, c in enumerate(blocks)}
    rels = []
    for (a, b), l in E.items():
        if chi[a] and chi[b]:
            if isdead(a, b, l):
                p, q = (a, b) if chi[a] > 0 else (b, a)
                g = R.elt(M.mul(M.S(l // 2, ((p, 1), (q, 1))), M.minus_one(p)))
                rels.append((g, find(p), find(q)))
            continue
        if chi[a] == 0 and chi[b] == 0:
            g = R.elt(M.mul(M.fox(M.relator(a, b, l), a), M.minus_one(a)))
            rels.append((g, find(choice[a][0]), find(choice[b][0])))
            continue
        w, x = (a, b) if chi[a] == 0 else (b, a)
        if choice[w][1] == (a, b):
            continue
        g = R.elt(M.mul(M.S(l // 2, ((w, 1), (x, 1))), M.minus_one(w)))
        rels.append((g, find(x), find(choice[w][0])))
    r = len(blocks)
    if not rels:
        return n * (r - 1)
    L = np.zeros((n * len(rels), n * r), dtype=complex)
    for i, (g, ca, cb) in enumerate(rels):
        L[i * n:(i + 1) * n, pos[ca] * n:(pos[ca] + 1) * n] += g
        L[i * n:(i + 1) * n, pos[cb] * n:(pos[cb] + 1) * n] -= g
    return n * (r - 1) - M.rank(L)


def run(trials, seed=20260919):
    rng = random.Random(seed)
    nprng = np.random.default_rng(seed)
    st = {"compared": 0, "agree": 0, "nonzero_h1": 0, "with_W": 0, "with_V": 0}
    while st["compared"] < trials:
        inst = M.random_instance(rng)
        if inst is None or not inst[1]:
            continue  # no edges: nothing to compare
        V, E, chi, mprime, lam = inst
        gens = M.coxeter_rep(V, mprime, nprng)
        gens = {x: lam[x] * gens[x] for x in V}
        t = complex(0.6 + 0.5 * rng.random(), 0.3 + 0.4 * rng.random())
        R = M.Rep(gens, chi, t)
        if M.reduced_h1(V, E, chi, R)[0] is None:
            continue  # same hypotheses as the main check (dominance, units survive)
        red = reduced_simplified(V, E, chi, R)
        full = M.full_h1(V, E, R)
        st["compared"] += 1
        st["agree"] += int(red == full)
        st["nonzero_h1"] += int(full > 0)
        st["with_W"] += int(any(chi[a] == 0 and chi[b] == 0 for (a, b) in E))
        st["with_V"] += int(any((chi[a] == 0) != (chi[b] == 0) for (a, b) in E))
    return st


if __name__ == "__main__":
    print("simplified D/V/W generators vs full H_1:", run(400))
