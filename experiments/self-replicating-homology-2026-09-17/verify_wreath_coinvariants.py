#!/usr/bin/env python3
"""Brute-force check of the coinvariant count behind
fully-self-replicating-fp-infinity-groups-are-acyclic.

For a graded vector space H = k.1 + H_+ (basis `degs` of H_+) and a permutation group
P on d points, P acts on H^{(x)d} by permuting tensor factors with the Koszul sign.
The script computes dim (H^{(x)d})_P in each degree by linear algebra over F_p
(p = 10007, prime to |P|) and compares it with the orbit count used in the proof:
one k for each P-orbit of basis tensors e_beta whose stabilizer acts by +1.
It also reports the "excess" E_n = dim(coinv)_n - dim H_n, which must vanish in every
degree n with dim H_n(R;k) finite when R = R wr_X P.
"""
import itertools

PR = 10007


def perm_sign(p):
    s, seen = 1, [False] * len(p)
    for i in range(len(p)):
        if not seen[i]:
            j, L = i, 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                L += 1
            if L % 2 == 0:
                s = -s
    return s


def close(gens, d):
    idp = tuple(range(d))
    G, frontier = {idp}, [idp]
    while frontier:
        nf = []
        for g in frontier:
            for h in gens:
                gh = tuple(h[g[i]] for i in range(d))
                if gh not in G:
                    G.add(gh)
                    nf.append(gh)
        frontier = nf
    return G


def act(g, beta, degs):
    """g sends factor at position i to position g[i]. Returns (sign, new beta)."""
    d = len(beta)
    new = [None] * d
    for i in range(d):
        new[g[i]] = beta[i]
    # Koszul sign: count inversions among odd-degree factors
    odd_pos = [i for i in range(d) if beta[i] >= 0 and degs[beta[i]] % 2 == 1]
    s = 1
    for a, b in itertools.combinations(odd_pos, 2):
        if g[a] > g[b]:
            s = -s
    return s, tuple(new)


def rank_mod(rows, ncols):
    m = [dict(r) for r in rows]
    basis = {}
    for r in m:
        r = {k: v % PR for k, v in r.items() if v % PR}
        while r:
            c = min(r)
            if c in basis:
                b = basis[c]
                f = r[c]
                for k, v in b.items():
                    r[k] = (r.get(k, 0) - f * v) % PR
                    if r[k] == 0:
                        del r[k]
            else:
                inv = pow(r[c], PR - 2, PR)
                r = {k: v * inv % PR for k, v in r.items()}
                basis[c] = r
                break
    return len(basis)


def coinvariants(degs, gens, d, maxdeg):
    # basis element: tuple of length d, entries -1 (unit) or index into degs
    idx = list(range(-1, len(degs)))
    tensors = list(itertools.product(idx, repeat=d))
    deg = lambda b: sum(degs[x] for x in b if x >= 0)
    out = {}
    G = close(gens, d)
    for n in range(0, maxdeg + 1):
        T = [b for b in tensors if deg(b) == n]
        pos = {b: i for i, b in enumerate(T)}
        rows = []
        for b in T:
            for g in gens:
                s, nb = act(g, b, degs)
                r = {pos[nb]: s % PR}
                r[pos[b]] = (r.get(pos[b], 0) - 1) % PR
                rows.append(r)
        dim_lin = len(T) - rank_mod(rows, len(T))
        # orbit count prediction
        seen, orb = set(), 0
        for b in T:
            if b in seen:
                continue
            O = set()
            good = True
            for g in G:
                s, nb = act(g, b, degs)
                O.add(nb)
                if nb == b and s == -1:
                    good = False
            seen |= O
            orb += good
        hn = 1 if n == 0 else sum(1 for x in degs if x == n)
        out[n] = (dim_lin, orb, dim_lin - hn)
    return out


def cyc(d):
    return tuple((i + 1) % d for i in range(d))


def run(name, gens, d, degs, maxdeg):
    res = coinvariants(degs, gens, d, maxdeg)
    print(f"{name}, d={d}, H_+ degrees {degs}:")
    ok = True
    for n, (lin, orb, exc) in res.items():
        ok &= lin == orb
        print(f"   deg {n}: dim coinv = {lin} (orbit count {orb}), excess E_{n} = {exc}")
    print("   linear algebra agrees with orbit count:", ok)
    return ok


if __name__ == "__main__":
    A5 = [(1, 2, 0, 3, 4), cyc(5)]
    A4 = [(1, 2, 0, 3), (0, 2, 3, 1)]
    S4 = [(1, 0, 2, 3), cyc(4)]
    Z3 = [cyc(3)]
    allok = True
    # one class in degree 1: pairs die, excess in degrees d-1 (support X minus a point) and d
    allok &= run("A_5", A5, 5, [1], 5)
    # one class in degree 2: excess from the pair e(x)e already in degree 4
    allok &= run("A_5", A5, 5, [2], 4)
    # two classes in degree 1: excess in degree 2 (e(x)e')
    allok &= run("A_5", A5, 5, [1, 1], 2)
    # classes in degrees 1 and 2: excess in degree 3
    allok &= run("A_4", A4, 4, [1, 2], 3)
    # S_4 with one odd class: every support >= 2 is killed (homology sphere allowed)
    allok &= run("S_4", S4, 4, [1], 4)
    allok &= run("S_4", S4, 4, [3], 12)
    # Z/3 = A_3: no swaps, one odd class gives excess already in degree 2
    allok &= run("Z/3", Z3, 3, [1], 3)
    print("ALL OK" if allok else "MISMATCH")
