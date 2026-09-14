#!/usr/bin/env python3
"""Independent verifier for F_p-labelled girth surfaces of the six hyperbolic rank-3 KMS families.

Shares no code with explore.py or kms_girth_search.py.  Vertex words are evaluated as products of 4x4 matrices
over F_p, not with the normal-form law used by the search:
  U3 vertex, letters of the first crossing type -> I+E03+E12, the other type -> I+E10-E23
  U4 vertex, designated x type -> I+E31, the other type -> I+E10-E23
These are psi(a), psi(b), psi(c) of kms-hb2-girth-surfaces-give-surface-subgroups-proof Step 0(b); by Step 0(c),(d)
there, psi is injective on U3(p) and U4(p) for odd p, so a vertex word is trivial in its vertex group exactly when
its matrix product is I mod p.
Checks per certificate: involutions, transitivity, orbit sizes 2*m_i, Euler characteristic, orientability,
labels in 1..p-1 on every side with both orientations recorded once, every vertex word = I mod p.
usage: verify_modp.py certificates.json [...]
"""
import sys, json

TABLE = {
    "HC2_1": ((3, 3, 4), ["U3", "U3", ("U4", 1)]),
    "HB2_2": ((3, 4, 4), ["U3", ("U4", 0), ("U4", 0)]),
    "HC2_2": ((3, 4, 4), ["U3", ("U4", 2), ("U4", 1)]),
    "HBC2_2": ((3, 4, 4), ["U3", ("U4", 2), ("U4", 0)]),
    "HB2_3": ((4, 4, 4), [("U4", 1), ("U4", 2), ("U4", 1)]),
    "HBC2_3": ((4, 4, 4), [("U4", 1), ("U4", 2), ("U4", 0)]),
}
OTHER = {0: (1, 2), 1: (0, 2), 2: (0, 1)}


def ident():
    return [[1 if r == c else 0 for c in range(4)] for r in range(4)]


def unip(entries, p):
    M = ident()
    for r, c, v in entries: M[r][c] = (M[r][c] + v) % p
    return M


def mmul(A, B, p):
    return [[sum(A[r][q] * B[q][c] for q in range(4)) % p for c in range(4)] for r in range(4)]


def mpow(M, e, p):
    e %= p
    R = ident()
    for _ in range(e): R = mmul(R, M, p)
    return R


allok = True; count = 0
for path in sys.argv[1:]:
    D = json.load(open(path)); fam = D["family"]; p = D["p"]; M, kinds = TABLE[fam]
    assert p % 2 == 1 and all(p % d for d in range(2, int(p ** 0.5) + 1))
    X3, Y3 = unip([(0, 3, 1), (1, 2, 1)], p), unip([(1, 0, 1), (2, 3, -1)], p)
    X4, Y4 = unip([(3, 1, 1)], p), unip([(1, 0, 1), (2, 3, -1)], p)
    for g in (X3, Y3, X4, Y4):
        assert mpow(g, p, p) == ident() and mpow(g, 1, p) != ident()
    for cert in D["certificates"]:
        T = cert["T"]; r = [cert["r0"], cert["r1"], cert["r2"]]; ok = {}
        ok["involutions"] = all(len(x) == T and all(x[x[t]] == t and x[t] != t for t in range(T)) for x in r)
        seen, st = {0}, [0]
        while st:
            u = st.pop()
            for k in range(3):
                if r[k][u] not in seen: seen.add(r[k][u]); st.append(r[k][u])
        ok["transitive"] = len(seen) == T
        nv, orb = 0, True
        for i in range(3):
            j, k = OTHER[i]; cov = set()
            for t in range(T):
                w, cur = [t], j
                for _ in range(2 * M[i]): w.append(r[cur][w[-1]]); cur = k if cur == j else j
                orb = orb and w[-1] == t and len(set(w[:-1])) == 2 * M[i]
                if t not in cov: nv += 1; cov.update(w)
        ok["orbits 2*m_i"] = orb
        col, st, ori = {0: 0}, [0], True
        while st:
            u = st.pop()
            for k in range(3):
                v = r[k][u]
                if v not in col: col[v] = 1 - col[u]; st.append(v)
                elif col[v] == col[u]: ori = False
        lab = {}
        for (k, t, s, x) in cert["labels"]:
            if r[k][t] == s and t < s: lab[(k, t)] = x
        ok["labels"] = (len(lab) == 3 * T // 2 == len(cert["labels"])
                        and all(isinstance(x, int) and 1 <= x <= p - 1 for x in lab.values()))
        words = True
        for i in range(3):
            j, k = OTHER[i]; kind = kinds[i]
            for t in range(T):
                g, u, cur = ident(), t, j
                for _ in range(2 * M[i]):
                    v = r[cur][u]; x = lab[(cur, min(u, v))]; e = x if u < v else -x
                    if kind == "U3": gen = X3 if cur == j else Y3
                    else: gen = X4 if cur == kind[1] else Y4
                    g = mmul(g, mpow(gen, e, p), p); u = v; cur = k if cur == j else j
                words = words and g == ident()
        ok["all vertex words = I mod p"] = words
        chi = nv - 3 * T // 2 + T
        good = all(ok.values()); allok = allok and good; count += 1
        print(fam, "p", p, "T", T, "surface", cert["surface_index"], "orientable", ori, "chi", chi, ok,
              "PASS" if good else "FAIL")
print("certificates checked:", count, "|", "ALL PASS" if allok else "SOME FAIL")
