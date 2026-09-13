#!/usr/bin/env sage -python
"""Units in characteristic 0 on the support pairs of Tabei's 52 one-sided F_2
units at radius 4 (arXiv:2608.00103v1, anc/census52.json).

  orbits          F_2 inverses over the 155-element box, orbits under the
                  automorphisms permuting {a^+-1, b^+-1}, product tables, and
                  2-adic depth-one feasibility at each residue;
                  writes census_pairs.json
  cases k F [TL]  localized systems for orbit representative k over F (QQ or
                  a prime). Case (i,j), i < j: u_k = 0 for k < i and i < k < j,
                  u_i = 1, u_j w = 1. Every unit with at least two support
                  elements, scaled, lies in exactly one case.
Group model: (s,t) with s a diagonal sign vector of determinant 1 and t in Z^3,
(s,t)(s',t') = (ss', t + s t'); a = ((1,-1,-1),(1,1,0)), b = ((-1,1,-1),(0,1,1)),
so a^2 = x = (1,(2,0,0)), b^2 = y = (1,(0,2,0)), (ab)^2 = z = (1,(0,0,-2)).
"""
import json, sys, time
from collections import deque
from sage.all import PolynomialRing, QQ, GF, matrix, vector
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

A = ((1, -1, -1), (1, 1, 0))
B = ((-1, 1, -1), (0, 1, 1))
GENS = {"a": A, "A": inv(A), "b": B, "B": inv(B)}
assert mul(A, A) == ((1, 1, 1), (2, 0, 0)) and mul(B, B) == ((1, 1, 1), (0, 2, 0))
assert mul(mul(A, B), mul(A, B)) == ((1, 1, 1), (0, 0, -2))
assert mul(mul(inv(B), mul(A, A)), B) == inv(mul(A, A))
assert mul(mul(inv(A), mul(B, B)), A) == inv(mul(B, B))

def ball(R):
    dist, word, dq = {ID: 0}, {ID: ""}, deque([ID])
    while dq:
        g = dq.popleft()
        if dist[g] == R:
            continue
        for L, s in GENS.items():
            h = mul(g, s)
            if h not in dist:
                dist[h], word[h] = dist[g] + 1, word[g] + L
                dq.append(h)
    return dist, word

def el(p):
    return (tuple(p[0]), tuple(p[1]))

def pair_system(S, T):
    cells, prod = {}, [[0] * len(T) for _ in S]
    for i, g in enumerate(S):
        for j, h in enumerate(T):
            prod[i][j] = cells.setdefault(mul(g, h), len(cells))
    return prod, len(cells), cells[ID]

mode = sys.argv[1]
if mode == "orbits":
    units = [[el(p) for p in u] for u in json.load(open("census52.json"))]
    box = sorted({el(p) for p in json.load(open("box_b4_syllable_intersect.json"))["box"]})
    dist, word = ball(4)
    stamp(f"{len(units)} units, box {len(box)}, |B(4)| = {len(dist)}")
    assert len(units) == 52 and len(box) == 155
    assert all(len(set(u)) == 21 and set(u) <= set(dist) for u in units)

    def f2_inverse(U):
        cols = {g: i for i, g in enumerate(box)}
        rows = {}
        for h in U:
            for g in box:
                rows.setdefault(mul(h, g), []).append(cols[g])
        keys = list(rows)
        M = matrix(GF(2), len(keys), len(box))
        for r, c in enumerate(keys):
            for i in rows[c]:
                M[r, i] += 1
        sol = M.solve_right(vector(GF(2), [1 if c == ID else 0 for c in keys]))
        assert M.right_kernel().dimension() == 0
        V = [g for g in box if sol[cols[g]] == 1]
        cnt = {}
        for h in U:
            for g in V:
                c = mul(h, g)
                cnt[c] = cnt.get(c, 0) ^ 1
        assert {c for c, e in cnt.items() if e} == {ID}, "convolution gate"
        return V

    auts = []
    for ia in "aAbB":
        for ib in "aAbB":
            pa, pb = GENS[ia], GENS[ib]
            if mul(mul(inv(pb), mul(pa, pa)), pb) != inv(mul(pa, pa)):
                continue
            if mul(mul(inv(pa), mul(pb, pb)), pa) != inv(mul(pb, pb)):
                continue
            sub = {"a": ia, "A": ia.swapcase(), "b": ib, "B": ib.swapcase()}
            img = {}
            for g, w in word.items():
                h = ID
                for L in w:
                    h = mul(h, GENS[sub[L]])
                img[g] = h
            if len(set(img.values())) == len(img):
                auts.append(img)
    stamp(f"automorphisms permuting the generators: {len(auts)}")
    assert len(auts) == 8, "Tabei, onesided_orbit_reps.py: 8 automorphisms"
    for img in auts:  # homomorphism spot gate on B(2) x B(2)
        for g in [g for g in word if len(word[g]) <= 2]:
            for h in [h for h in word if len(word[h]) <= 2]:
                assert mul(img[g], img[h]) == img[mul(g, h)]
    dist8 = ball(8)[0]
    census = {frozenset(u) for u in units}
    left, reps = set(census), []
    while left:
        seed = min(left, key=sorted)
        orb = {frozenset(img[g] for g in seed) for img in auts}
        assert orb <= census, "orbit leaves the census"
        left -= orb
        reps.append((sorted(seed), len(orb)))
    out = []
    for k, (S, size) in enumerate(reps):
        T = sorted(f2_inverse(S))
        prod, K, eid = pair_system(S, T)
        triv = [(i, j) for i in range(21) for j in range(len(T)) if prod[i][j] == eid]
        n, m = len(S), len(T)
        J = matrix(GF(2), K + 1, n + m)
        F = [0] * (K + 1)
        for i in range(n):
            for j in range(m):
                J[prod[i][j], i] += 1
                J[prod[i][j], n + j] += 1
                F[prod[i][j]] += 1
        F[eid] -= 1
        for i in range(n):
            J[K, i] = 1
        F[K] = n - 1
        assert all(f % 2 == 0 for f in F)
        rhs = vector(GF(2), [(-f // 2) % 2 for f in F])
        rk = J.rank()
        try:
            J.solve_right(rhs)
            depth1 = f"feasible, kernel dimension {n + m - rk}"
        except ValueError:
            depth1 = "infeasible: the residue has no Z_2-lift on this pair"
        stamp(f"orbit {k}: size {size}, |T| = {m}, radius of T {max(ball(8)[0].get(g, 99) for g in T)}, "
              f"cells {K}, trivial pairs {len(triv)}, J mod 2 rank {rk}/{n + m}, depth one {depth1}")
        out.append({"size": size, "S": [list(map(list, g)) for g in S],
                    "T": [list(map(list, g)) for g in T], "prod": prod, "K": K,
                    "eid": eid, "trivial_pairs": triv})
    assert sum(o["size"] for o in out) == 52
    json.dump(out, open("census_pairs.json", "w"))
elif mode == "cases":
    k, Fs = int(sys.argv[2]), sys.argv[3]
    TL = int(sys.argv[4]) if len(sys.argv) > 4 else 1800
    Tsel = sys.argv[5] if len(sys.argv) > 5 else "inv"
    F = QQ if Fs == "QQ" else GF(int(Fs))
    d = json.load(open("census_pairs.json"))[k]
    if Tsel == "box":  # every inverse support of a unit supported in B(4) lies in the box
        S = [el(p) for p in d["S"]]
        T = sorted({el(p) for p in json.load(open("box_b4_syllable_intersect.json"))["box"]})
        prod, K, eid = pair_system(S, T)
        Fs = Fs + "box"
    else:
        prod, K, eid = d["prod"], d["K"], d["eid"]
    n, m = len(d["S"]), len(prod[0])
    stamp(f"orbit {k}: |S| = {n}, |T| = {m} ({Tsel}), cells {K}")
    names = [f"u{i}" for i in range(n)] + [f"v{j}" for j in range(m)] + ["w"]
    R = PolynomialRing(F, names, order="degrevlex")
    g = R.gens()
    nonempty, timeouts = [], []
    for i in range(n):
        for j in range(i + 1, n):
            u = [R(1) if a == i else (g[a] if a > j or a == j else R(0)) for a in range(n)]
            eqs = [R(0)] * K
            for a in range(n):
                if u[a] != 0:
                    for b in range(m):
                        eqs[prod[a][b]] += u[a] * g[n + b]
            eqs[eid] -= 1
            eqs.append(g[j] * g[-1] - 1)
            try:
                alarm(TL)
                G = slimgb(R.ideal([e for e in eqs if e != 0]))
                cancel_alarm()
            except AlarmInterrupt:
                timeouts.append((i, j))
                stamp(f"orbit {k} {Fs} case ({i},{j}): TIMEOUT {TL}s")
                continue
            if any(p.is_constant() and p != 0 for p in G):
                continue
            nonempty.append((i, j))
            stamp(f"orbit {k} {Fs} case ({i},{j}): GB size {len(G)}, dim {sdim(G)}, vdim {vdim(G)}")
            with open(f"census_gb_{k}_{Fs}_{i}_{j}.txt", "w") as fh:
                fh.write("\n".join(str(p) for p in G))
    stamp(f"orbit {k} {Fs}: nonempty cases {nonempty}; timeouts {timeouts}")
print("DONE", flush=True)
