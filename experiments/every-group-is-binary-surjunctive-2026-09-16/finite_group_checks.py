#!/usr/bin/env python3
"""Sanity checks of the three-address kill lemmas on finite groups (evidence only, not the proof).

For each group G and each ordered triple M = (m0, m1, m2) of distinct elements:
 (i)   brute-force injectivity (|G| <= 12) for all 17 normalized rules; check the predictions
       - T1 rule (majority): never injective;
       - Lemma C rules: injective  =>  m_r m_p^-1 in <m_q m_p^-1> for every applicable (p,q,r);
       - selector AND/OR rules: injective  =>  M is a right coset of a subgroup of order 3;
 (ii)  Lemma C direct: tau(1_S) == tau(const) for S = <u>, u = m_q m_p^-1, when v = m_r m_p^-1 not in S;
 (iii) flip lemma for selector AND/OR rules: some x has tau(x) = tau(x + delta_e)
       iff M is not a right coset of an order-3 subgroup (checked by brute force on e M^-1 M).
"""
import itertools, sys
import numpy as np
from three_address_classify import classify, lemma_c_triples, selector_and_or

def closure(gens):
    n = len(gens[0])
    e = tuple(range(n))
    elems = [e]
    seen = {e}
    i = 0
    while i < len(elems):
        g = elems[i]
        for s in gens:
            h = tuple(s[g[j]] for j in range(n))  # h = s o g
            if h not in seen:
                seen.add(h)
                elems.append(h)
        i += 1
    index = {g: k for k, g in enumerate(elems)}
    N = len(elems)
    mult = np.zeros((N, N), dtype=np.int64)
    for a in range(N):
        for b in range(N):
            ga, gb = elems[a], elems[b]
            mult[a, b] = index[tuple(ga[gb[j]] for j in range(n))]  # a*b = a o b
    inv = np.zeros(N, dtype=np.int64)
    for a in range(N):
        inv[a] = int(np.where(mult[a] == 0)[0][0])
    return mult, inv

def cyc(n):
    return [tuple((i + 1) % n for i in range(n))]

def dihedral(n):
    return [tuple((i + 1) % n for i in range(n)), tuple((-i) % n for i in range(n))]

def perm_from_cycles(n, cycles):
    p = list(range(n))
    for c in cycles:
        for i in range(len(c)):
            p[c[i]] = c[(i + 1) % len(c)]
    return tuple(p)

def product_gens(g1, g2):
    n1, n2 = len(g1[0]), len(g2[0])
    out = [tuple(list(s) + [n1 + j for j in range(n2)]) for s in g1]
    out += [tuple(list(range(n1)) + [n1 + s[j] for j in range(n2)]) for s in g2]
    return out

def groups_small():
    gs = {}
    for n in range(2, 13):
        gs["Z%d" % n] = cyc(n)
    for n in range(3, 7):
        gs["D%d" % n] = dihedral(n)
    gs["Z2xZ2"] = product_gens(cyc(2), cyc(2))
    gs["Z2xZ4"] = product_gens(cyc(2), cyc(4))
    gs["Z2xZ6"] = product_gens(cyc(2), cyc(6))
    gs["Z3xZ3"] = product_gens(cyc(3), cyc(3))
    gs["Z2^3"] = product_gens(product_gens(cyc(2), cyc(2)), cyc(2))
    gs["A4"] = [perm_from_cycles(4, [(0, 1, 2)]), perm_from_cycles(4, [(0, 1), (2, 3)])]
    # Q8 via its regular representation: i, j acting on 8 points (1,i,-1,-i,j,k,-j,-k) indices
    gs["Q8"] = [perm_from_cycles(8, [(0, 1, 2, 3), (4, 5, 6, 7)]), perm_from_cycles(8, [(0, 4, 2, 6), (1, 7, 3, 5)])]
    # Dic3 = Z3 x| Z4: pairs (sigma in S3, t in Z4) with sign(sigma) = t mod 2
    gs["Dic3"] = [perm_from_cycles(7, [(0, 1, 2)]), perm_from_cycles(7, [(1, 2), (3, 4, 5, 6)])]
    return gs

def groups_large():
    return {
        "S4": [perm_from_cycles(4, [(0, 1, 2, 3)]), perm_from_cycles(4, [(0, 1)])],
        "A5": [perm_from_cycles(5, [(0, 1, 2, 3, 4)]), perm_from_cycles(5, [(0, 1, 2)])],
        "D8": dihedral(8),
        "Z3xS3": product_gens(cyc(3), dihedral(3)),
    }

def image_codes(mult, M, mu, X):
    """X: (2^N, N) 0/1 array of all configurations; returns packed image codes."""
    N = mult.shape[0]
    mu = np.array(mu, dtype=np.int64)
    Y = np.empty_like(X)
    for h in range(N):
        i0, i1, i2 = mult[h, M[0]], mult[h, M[1]], mult[h, M[2]]
        Y[:, h] = mu[X[:, i0] * 4 + X[:, i1] * 2 + X[:, i2]]
    w = (1 << np.arange(N, dtype=np.int64))
    return Y @ w

def tau(mult, M, mu, x):
    N = mult.shape[0]
    return np.array([mu[x[mult[h, M[0]]] * 4 + x[mult[h, M[1]]] * 2 + x[mult[h, M[2]]]] for h in range(N)])

def cyclic_subgroup(mult, u):
    S, g = [0], u
    while g != 0:
        S.append(int(g))
        g = mult[g, u]
    return set(S)

def right_coset_of_order3(mult, inv, M):
    p = M[0]
    H = {int(mult[m, inv[p]]) for m in M}
    if 0 not in H:
        return False
    return all(int(mult[a, b]) in H for a in H for b in H)

def flip_invisible_exists(mult, inv, M, mu):
    """Is there x with tau(x) = tau(x + delta_e)? Brute force over the sites e M^-1 M."""
    readers = [int(inv[m]) for m in M]  # sites h with h m = e for some m in M
    region = sorted({int(mult[h, m]) for h in readers for m in M})
    others = [s for s in region if s != 0]
    for bits in itertools.product((0, 1), repeat=len(others)):
        x = {s: b for s, b in zip(others, bits)}
        ok = True
        for h in readers:
            vals0, vals1 = [], []
            for m in M:
                s = int(mult[h, m])
                vals0.append(0 if s == 0 else x[s])
                vals1.append(1 if s == 0 else x[s])
            if mu[vals0[0] * 4 + vals0[1] * 2 + vals0[2]] != mu[vals1[0] * 4 + vals1[1] * 2 + vals1[2]]:
                ok = False
                break
        if ok:
            return True
    return False

def run(groups, full):
    rows = classify()
    bad = 0
    for name, gens in groups.items():
        mult, inv = closure(gens)
        N = mult.shape[0]
        X = None
        if full:
            X = ((np.arange(1 << N)[:, None] >> np.arange(N)[None, :]) & 1).astype(np.int64)
        stats = {"inj": 0, "triples": 0}
        for M in itertools.permutations(range(N), 3):
            stats["triples"] += 1
            rc3 = right_coset_of_order3(mult, inv, M)
            for mu, kind in rows:
                trip = lemma_c_triples(mu)
                # (ii) Lemma C direct check
                for (p, q, r) in trip:
                    u = int(mult[M[q], inv[M[p]]]); v = int(mult[M[r], inv[M[p]]])
                    S = cyclic_subgroup(mult, u)
                    if v not in S:
                        x = np.array([1 if g in {int(mult[s, M[p]]) for s in S} else 0 for g in range(N)])
                        # x = 1_{S m_p}: the coset background of tau' = tau o R_{m_p}^-1 moved back to tau
                        y0, y1, yc0, yc1 = tau(mult, M, mu, x), tau(mult, M, mu, 1 - x), tau(mult, M, mu, np.zeros(N, dtype=int)), tau(mult, M, mu, np.ones(N, dtype=int))
                        pq = [0, 0, 0]; pq[p] = 1; pq[q] = 1; er = [0, 0, 0]; er[r] = 1
                        vpq, ver = mu[pq[0] * 4 + pq[1] * 2 + pq[2]], mu[er[0] * 4 + er[1] * 2 + er[2]]
                        c0 = vpq == ver == mu[0]; c1 = vpq == ver == mu[7]
                        if (c0 and not np.array_equal(y0, yc0)) or (c1 and not np.array_equal(y1, yc1)) or not (c0 or c1):
                            bad += 1; print("LEMMA C FAIL", name, M, mu, (p, q, r))
                if kind == "A":
                    fe = flip_invisible_exists(mult, inv, M, mu)
                    if fe == rc3:
                        bad += 1; print("FLIP LEMMA FAIL", name, M, mu, fe, rc3)
                if full:
                    codes = image_codes(mult, M, mu, X)
                    inj = len(np.unique(codes)) == (1 << N)
                    if inj:
                        stats["inj"] += 1
                        if kind == "T1":
                            bad += 1; print("T1 FAIL", name, M, mu)
                        if kind == "A" and not rc3:
                            bad += 1; print("A FAIL", name, M, mu)
                        for (p, q, r) in trip:
                            u = int(mult[M[q], inv[M[p]]]); v = int(mult[M[r], inv[M[p]]])
                            if v not in cyclic_subgroup(mult, u):
                                bad += 1; print("C FAIL", name, M, mu, (p, q, r))
        print(name, "order", N, stats); sys.stdout.flush()
    return bad

if __name__ == "__main__":
    # usage: finite_group_checks.py [GROUP ...]; small groups get the full injectivity check
    small, large = groups_small(), groups_large()
    names = sys.argv[1:] or list(small) + list(large)
    bad = 0
    for nm in names:
        if nm in small:
            bad += run({nm: small[nm]}, full=True)
        else:
            bad += run({nm: large[nm]}, full=False)
    print("TOTAL FAILURES", bad, "groups", " ".join(names))
