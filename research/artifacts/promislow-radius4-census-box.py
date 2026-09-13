#!/usr/bin/env sage -python
"""Inverse-support bounds on the seven census pairs, valid over every field,
and the case split on the enlarged pairs.

  bounds          for each orbit representative S (census_pairs.json):
                  adj(S): elements r_i n_e, e in the support of the (i,0)
                          cofactor of the generic matrix Phi(u), supp u in S;
                  box(S): elements g with l^(m)_i(g) <= max_{h in S} l^(m)_i(h)
                          for i = 0,1,2 and -MR <= m <= MR (syllable lengths of
                          the amalgams P -> D_infty, as in Tabei's box);
                  checks T (the F_2 inverse) is in both; writes sbox_pairs.json
  cases k sel TL  case split of census.py over QQ on (S, T') with T' = adj(S),
                  box(S) or their intersection (sel = adj, box, both)
"""
import json, sys, time
from itertools import permutations
from sage.all import PolynomialRing, QQ
from sage.libs.singular.function_factory import singular_function
from cysignals.alarm import alarm, cancel_alarm, AlarmInterrupt

slimgb = singular_function("slimgb")
vdim = singular_function("vdim")
sdim = singular_function("dim")
T0 = time.time()

def stamp(msg):
    print(f"{msg}  [{time.time() - T0:.1f}s]", flush=True)

ID = ((1, 1, 1), (0, 0, 0))

def mul(g, h):
    return (tuple(p * q for p, q in zip(g[0], h[0])),
            tuple(t + p * q for t, p, q in zip(g[1], g[0], h[1])))

def inv(g):
    return (g[0], tuple(-p * t for p, t in zip(g[0], g[1])))

def el(p):
    return (tuple(p[0]), tuple(p[1]))

A = ((1, -1, -1), (1, 1, 0))
B = ((-1, 1, -1), (0, 1, 1))
assert mul(mul(inv(B), mul(A, A)), B) == inv(mul(A, A))
assert mul(mul(inv(A), mul(B, B)), A) == inv(mul(B, B))
REPS = [ID, A, B, mul(A, B)]
SIGNS = [r[0] for r in REPS]

def column(g):
    """g r_j = r_i n_e for j = 0..3, with n_e = (1, (2 e_0, 2 e_1, -2 e_2))."""
    out = []
    for r in REPS:
        h = mul(g, r)
        i = SIGNS.index(h[0])
        n = mul(inv(REPS[i]), h)
        assert n[0] == (1, 1, 1) and all(t % 2 == 0 for t in n[1])
        out.append((i, (n[1][0] // 2, n[1][1] // 2, (-n[1][2]) // 2)))
    return out

def n_of(e):
    return ((1, 1, 1), (2 * e[0], 2 * e[1], -2 * e[2]))

def adj_bound(S):
    E = [[set() for _ in range(4)] for _ in range(4)]
    for g in S:
        for j, (i, e) in enumerate(column(g)):
            E[i][j].add(e)
    out = set()
    for i in range(4):  # adj_{i0}: delete row 0 and column i
        cols = [c for c in range(4) if c != i]
        sup = set()
        for p in permutations(cols):
            acc = {(0, 0, 0)}
            for row, col in zip((1, 2, 3), p):
                acc = {tuple(a + b for a, b in zip(x, y)) for x in acc for y in E[row][col]}
            sup |= acc
        out |= {mul(REPS[i], n_of(e)) for e in sup}
    return out

def syl(d, m):
    n, e = d
    return 2 * abs(n) if e == 0 else min(2 * abs(m - n) + 1, 2 * abs(m + 1 - n) + 1)

def pi(g, i):
    return (g[1][i], 0 if g[0][i] == 1 else 1)

def box_bound(S, MR=40):
    M0 = [max(syl(pi(g, i), 0) for g in S) for i in range(3)]
    rng = [range(-(M0[i] // 2) - 2, M0[i] // 2 + 3) for i in range(3)]
    par = {r[0]: tuple(t % 2 for t in r[1]) for r in REPS}
    cand = [(s, (t0, t1, t2)) for s in SIGNS for t0 in rng[0] for t1 in rng[1] for t2 in rng[2]
            if (t0 % 2, t1 % 2, t2 % 2) == par[s]]
    for i in range(3):  # just outside the range, and farther out, box^(0) fails
        assert all(syl((n, e), 0) > M0[i] for n in (rng[i][0] - 1, rng[i][-1] + 1) for e in (0, 1))
    box, sizes = set(cand), []
    for m in range(-MR, MR + 1):
        M = [max(syl(pi(g, i), m) for g in S) for i in range(3)]
        box = {g for g in box if all(syl(pi(g, i), m) <= M[i] for i in range(3))}
        sizes.append(len(box))
    return box, sizes

mode = sys.argv[1]
pairs = json.load(open("census_pairs.json"))
if mode == "bounds":
    out = []
    for k, d in enumerate(pairs):
        S = [el(p) for p in d["S"]]
        T = {el(p) for p in d["T"]}
        adj = adj_bound(S)
        box, sizes = box_bound(S)
        both = adj & box
        stamp(f"orbit {k}: |T| = {len(T)}, |adj(S)| = {len(adj)}, |box(S)| = {len(box)} "
              f"(sizes at m = -40, -1, 0, 1, 40 after intersecting: {sizes[0]}, {sizes[39]}, {sizes[40]}, {sizes[41]}, {sizes[80]}), "
              f"|both| = {len(both)}, T in adj {T <= adj}, T in box {T <= box}, "
              f"S^-1 in adj {set(map(inv, S)) <= adj}, S^-1 in box {set(map(inv, S)) <= box}")
        out.append({k2: sorted([list(map(list, g)) for g in v]) for k2, v in
                    (("adj", adj), ("box", box), ("both", both))})
    json.dump(out, open("sbox_pairs.json", "w"))
elif mode == "cases":
    k, sel, TL = int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
    S = [el(p) for p in pairs[k]["S"]]
    T = [el(p) for p in json.load(open("sbox_pairs.json"))[k][sel]]
    assert {el(p) for p in pairs[k]["T"]} <= set(T)
    cells, prod = {}, [[0] * len(T) for _ in S]
    for i, g in enumerate(S):
        for j, h in enumerate(T):
            prod[i][j] = cells.setdefault(mul(g, h), len(cells))
    K, eid, n, m = len(cells), cells[ID], len(S), len(T)
    stamp(f"orbit {k}: |S| = {n}, |T'| = {m} ({sel}), cells {K}")
    R = PolynomialRing(QQ, [f"u{i}" for i in range(n)] + [f"v{j}" for j in range(m)] + ["w"],
                       order="degrevlex")
    g = R.gens()
    nonempty, timeouts, worst = [], [], (0, None)
    for i in range(n):
        for j in range(i + 1, n):
            u = [R(1) if a == i else (g[a] if a >= j else R(0)) for a in range(n)]
            eqs = [R(0)] * K
            for a in range(n):
                if u[a] != 0:
                    for b in range(m):
                        eqs[prod[a][b]] += u[a] * g[n + b]
            eqs[eid] -= 1
            eqs.append(g[j] * g[-1] - 1)
            t0 = time.time()
            try:
                alarm(TL)
                G = slimgb(R.ideal([e for e in eqs if e != 0]))
                cancel_alarm()
            except AlarmInterrupt:
                timeouts.append((i, j))
                stamp(f"orbit {k} {sel} case ({i},{j}): TIMEOUT {TL}s")
                continue
            worst = max(worst, (time.time() - t0, (i, j)))
            if any(p.is_constant() and p != 0 for p in G):
                continue
            nonempty.append((i, j))
            stamp(f"orbit {k} {sel} case ({i},{j}): GB size {len(G)}, dim {sdim(G)}, vdim {vdim(G)}")
        stamp(f"orbit {k} {sel}: i = {i} done")
    stamp(f"orbit {k} {sel}: nonempty cases {nonempty}; timeouts {timeouts}; slowest {worst}")
print("DONE", flush=True)
