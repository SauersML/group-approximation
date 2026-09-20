"""Representation census for the corrected Sigma^1 conjecture on non-star dead cuts.

For a labelled graph Gamma (all vertices living) and an integer character chi, the
dead-cut Laplacian of artin-sigma1-equals-dead-cut-laplacian-surjectivity has one
D generator per crossing dead edge {p, q} (chi(p) > 0, label 2k):
    Novikov:  g = S_k(pq) (p - 1),        level 0:  sigma = S_k(pq).
For a finite-dimensional complex representation pi of A_Gamma we compute
    c0(pi)  = dim coker (L_0 (x) pi)                     (pi restricted to H = ker chi)
    ct(pi)  = dim coker (L_chi (x) pi_s), pi_s(g) = s^chi(g) pi(g), s random.
c0 > 0 certifies that L_0 is not onto over Z[H] (numerically).
ct > 0 certifies [chi] not in Sigma^1 (numerically): N_chi -> M_n(C((s))) is a ring map.
A *candidate counterexample* is an instance where some pi has c0 > 0 but every pi tried
has ct = 0.

Representations: Coxeter reflection representations of quotients W(m'), m'_e | l_e,
with random angles cos(j pi / m') and random off-edge parameters, times scalar
characters, and tensor products of two of these.
"""
import itertools
import math
import random
import sys

import numpy as np


def rank(M, tol=1e-8):
    if M.size == 0:
        return 0
    s = np.linalg.svd(M, compute_uv=False)
    return int((s > tol * max(1.0, s[0])).sum())


def blocks_of(V, E, chi):
    par = {v: v for v in V}

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    dead = []
    for (a, b), l in E.items():
        if l % 2 == 0 and l >= 4 and chi[a] + chi[b] == 0:
            dead.append((a, b, l))
        else:
            par[f(a)] = f(b)
    comp = {v: f(v) for v in V}
    return comp, dead


def instance_data(V, E, chi):
    comp, dead = blocks_of(V, E, chi)
    blocks = sorted(set(comp.values()))
    cross = []
    for a, b, l in dead:
        if comp[a] == comp[b]:
            continue
        p, q = (a, b) if chi[a] > 0 else (b, a)
        cross.append((p, q, l // 2))
    return comp, blocks, cross


def is_star(cross):
    verts = set(x for e in cross for x in e[:2])
    return any(all(v in e[:2] for e in cross) for v in verts)


def block_graph_connected(blocks, comp, cross):
    par = {b: b for b in blocks}

    def f(x):
        while par[x] != x:
            x = par[x]
        return x

    for p, q, k in cross:
        par[f(comp[p])] = f(comp[q])
    return len({f(b) for b in blocks}) == 1


def coxeter_rep(V, E, rng):
    n = len(V)
    idx = {x: i for i, x in enumerate(V)}
    B = np.eye(n, dtype=complex)
    for (a, b) in itertools.combinations(V, 2):
        if (a, b) in E or (b, a) in E:
            l = E.get((a, b), E.get((b, a)))
            divs = [d for d in range(2, l + 1) if l % d == 0]
            m = rng.choice(divs)
            js = [j for j in range(1, m) if math.gcd(j, m) == 1]
            j = rng.choice(js)
            val = -math.cos(j * math.pi / m)
            # non-symmetric scaling keeps the product B_ab B_ba = cos^2
            sc = complex(rng.uniform(0.5, 2.0), rng.uniform(-0.5, 0.5))
            B[idx[a], idx[b]] = val * sc
            B[idx[b], idx[a]] = val / sc
        else:
            B[idx[a], idx[b]] = complex(-1 - 2 * rng.random(), rng.uniform(-1, 1))
            B[idx[b], idx[a]] = complex(-1 - 2 * rng.random(), rng.uniform(-1, 1))
    mats = {}
    for x in V:
        M = np.eye(n, dtype=complex)
        M[idx[x], :] -= 2 * B[idx[x], :]
        mats[x] = M
    return mats


def odd_classes(V, E):
    par = {v: v for v in V}

    def f(x):
        while par[x] != x:
            x = par[x]
        return x

    for (a, b), l in E.items():
        if l % 2:
            par[f(a)] = f(b)
    return {v: f(v) for v in V}


def scalar_char(V, E, rng):
    cl = odd_classes(V, E)
    vals = {}
    for c in set(cl.values()):
        if rng.random() < 0.5:
            m = rng.choice([1, 2, 3, 4, 5, 6, 8, 10, 12])
            vals[c] = np.exp(2j * math.pi * rng.randrange(m) / m)
        else:
            vals[c] = np.exp(complex(rng.uniform(-0.3, 0.3), rng.uniform(0, 2 * math.pi)))
    return {v: vals[cl[v]] for v in V}


def check_relations(V, E, mats, tol=1e-6):
    for (a, b), l in E.items():
        A, B = mats[a], mats[b]
        P1 = np.eye(A.shape[0], dtype=complex)
        P2 = np.eye(A.shape[0], dtype=complex)
        for i in range(l):
            P1 = P1 @ (A if i % 2 == 0 else B)
            P2 = P2 @ (B if i % 2 == 0 else A)
        if np.abs(P1 - P2).max() > tol * max(1, np.abs(P1).max()):
            return False
    return True


def random_rep(V, E, rng, kind):
    if kind == "cox":
        m = coxeter_rep(V, E, rng)
        lam = scalar_char(V, E, rng)
        return {x: lam[x] * m[x] for x in V}
    if kind == "scalar":
        lam = scalar_char(V, E, rng)
        return {x: np.array([[lam[x]]]) for x in V}
    if kind == "tensor":
        m1 = random_rep(V, E, rng, "cox")
        m2 = random_rep(V, E, rng, "cox")
        return {x: np.kron(m1[x], m2[x]) for x in V}
    raise ValueError(kind)


def Smat(X, k):
    R = np.eye(X.shape[0], dtype=complex)
    P = np.eye(X.shape[0], dtype=complex)
    for _ in range(k - 1):
        P = P @ X
        R = R + P
    return R


def cokers(blocks, comp, cross, chi, mats, s):
    n = next(iter(mats.values())).shape[0]
    r = len(blocks)
    pos = {b: i for i, b in enumerate(blocks)}
    I = np.eye(n, dtype=complex)
    L0 = np.zeros((n * len(cross), n * r), dtype=complex)
    Lt = np.zeros((n * len(cross), n * r), dtype=complex)
    for i, (p, q, k) in enumerate(cross):
        sig = Smat(mats[p] @ mats[q], k)
        g = sig @ (s ** chi[p] * mats[p] - I)
        a, b = pos[comp[p]], pos[comp[q]]
        for M, blk in ((L0, sig), (Lt, g)):
            M[i * n:(i + 1) * n, a * n:(a + 1) * n] += blk
            M[i * n:(i + 1) * n, b * n:(b + 1) * n] -= blk
    # cokernel inside K_r: columns act on the right; dim coker = n(r-1) - rank
    return n * (r - 1) - rank(L0), n * (r - 1) - rank(Lt)


def random_graph(rng, nv):
    V = [chr(ord('a') + i) for i in range(nv)]
    E = {}
    for a, b in itertools.combinations(V, 2):
        if rng.random() < 0.8:
            E[(a, b)] = rng.choice([2, 2, 3, 4, 4, 4, 6, 6, 8, 10])
    cl = odd_classes(V, E)
    vals = {}
    for c in set(cl.values()):
        vals[c] = rng.choice([1, 1, 1, -1, -1, -1, 2, -2])
    chi = {v: vals[cl[v]] for v in V}
    return V, E, chi


def circuit_rank(V, E):
    par = {v: v for v in V}

    def f(x):
        while par[x] != x:
            x = par[x]
        return x

    for a, b in E:
        par[f(a)] = f(b)
    return len(E) - len(V) + len({f(v) for v in V})


def analyse(V, E, chi, rng, nreps=40):
    comp, blocks, cross = instance_data(V, E, chi)
    res = {"c0": 0, "ct": 0, "c0_only_reps": 0, "reps": 0}
    for i in range(nreps):
        kind = ["scalar", "cox", "cox", "tensor"][i % 4]
        mats = random_rep(V, E, rng, kind)
        if not check_relations(V, E, mats):
            raise RuntimeError("relations fail")
        s = complex(rng.uniform(0.3, 0.9), rng.uniform(0.2, 0.7))
        c0, ct = cokers(blocks, comp, cross, chi, mats, s)
        res["reps"] += 1
        res["c0"] = max(res["c0"], c0)
        res["ct"] = max(res["ct"], ct)
        if c0 > 0 and ct == 0:
            res["c0_only_reps"] += 1
        if res["ct"] > 0 and i >= 3:
            break
    return res, blocks, cross


def main(ninst, seed, nv):
    rng = random.Random(seed)
    seen = set()
    stats = {"instances": 0, "nonmember_certified": 0, "L0_witness_no_twisted": 0,
             "no_witness_either": 0}
    cands, silent = [], []
    tries = 0
    while stats["instances"] < ninst and tries < 200 * ninst:
        tries += 1
        V, E, chi = random_graph(rng, nv)
        comp, blocks, cross = instance_data(V, E, chi)
        if len(blocks) < 2 or not cross or is_star(cross):
            continue
        if not block_graph_connected(blocks, comp, cross):
            continue
        if circuit_rank(V, E) < 3:
            continue
        key = (tuple(sorted(E.items())), tuple(sorted(chi.items())))
        if key in seen:
            continue
        seen.add(key)
        stats["instances"] += 1
        res, blocks, cross = analyse(V, E, chi, rng)
        if res["ct"] > 0:
            stats["nonmember_certified"] += 1
        elif res["c0"] > 0:
            stats["L0_witness_no_twisted"] += 1
            cands.append((E, chi, cross, res))
        else:
            stats["no_witness_either"] += 1
            silent.append((E, chi, cross, res))
    print("seed", seed, "nv", nv, stats, flush=True)
    for c in cands[:20]:
        print("CANDIDATE", c, flush=True)
    for c in silent[:20]:
        print("SILENT", c, flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
