#!/usr/bin/env python3
"""Independent verifier for integer-labelled girth surfaces of the six hyperbolic rank-3 KMS families.

Shares no code with kms_girth_search.py.  Vertex words are evaluated with integer matrices, not with the
normal-form law used by the search:
  U3 vertex <x,y | [x,y,x],[x,y,y]>:            x -> I+E03+E12, y -> I+E10-E23   (faithful over Z on N_3)
  U4 vertex <x,y | [x,y,x],[x,y,y,x],[x,y,y,y]>: x -> I+E31,     y -> I+E10-E23   (faithful over Z on N_4)
Faithfulness over Z: the symbolic entries printed in verify.log (item 9) for <a,b> and <c,b>.
Checks per certificate: involutions, transitivity, orbit sizes 2*m_i, Euler characteristic, orientability,
nonzero integer labels (with the primes dividing them), every vertex word = I over Z.
usage: verify_kms_certificates.py search-output.json [...]
"""
import sys, json

TABLE = {                                   # (m_0,m_1,m_2), vertex kinds; U4 kind carries the x edge type
    "HC2_1": ((3, 3, 4), ["U3", "U3", ("U4", 1)]),
    "HB2_2": ((3, 4, 4), ["U3", ("U4", 0), ("U4", 0)]),
    "HC2_2": ((3, 4, 4), ["U3", ("U4", 2), ("U4", 1)]),
    "HBC2_2": ((3, 4, 4), ["U3", ("U4", 2), ("U4", 0)]),
    "HB2_3": ((4, 4, 4), [("U4", 1), ("U4", 2), ("U4", 1)]),
    "HBC2_3": ((4, 4, 4), [("U4", 1), ("U4", 2), ("U4", 0)]),
}
OTHER = {0: (1, 2), 1: (0, 2), 2: (0, 1)}

def mat(entries):
    M = [[int(r == c) for c in range(4)] for r in range(4)]
    for r, c, v in entries: M[r][c] += v
    return M
def mmul(A, B): return [[sum(A[r][q] * B[q][c] for q in range(4)) for c in range(4)] for r in range(4)]
def mpow(M, e):
    N = [[M[r][c] - int(r == c) for c in range(4)] for r in range(4)]
    assert all(v == 0 for row in mmul(N, N) for v in row)
    return [[int(r == c) + e * N[r][c] for c in range(4)] for r in range(4)]
ID = mat([])
U3X, U3Y = mat([(0, 3, 1), (1, 2, 1)]), mat([(1, 0, 1), (2, 3, -1)])
U4X, U4Y = mat([(3, 1, 1)]), mat([(1, 0, 1), (2, 3, -1)])
def comm(A, B): return mmul(mmul(mpow(A, -1), mpow(B, -1)), mmul(A, B))
def lc(*xs):
    r = xs[0]
    for x in xs[1:]: r = comm(r, x)
    return r
models_ok = (lc(U3X, U3Y, U3X) == ID and lc(U3X, U3Y, U3Y) == ID and lc(U4X, U4Y, U4X) == ID
             and lc(U4X, U4Y, U4Y, U4X) == ID and lc(U4X, U4Y, U4Y, U4Y) == ID)
print("matrix models satisfy the U3 and U4 relators over Z:", models_ok)

def primes_of(n):
    n, out, d = abs(n), set(), 2
    while d * d <= n:
        while n % d == 0: out.add(d); n //= d
        d += 1
    if n > 1: out.add(n)
    return out

allok = models_ok; count = 0
for path in sys.argv[1:]:
    D = json.load(open(path)); fam = D["family"]; M, kinds = TABLE[fam]
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
        lab = {(k, t): x for (k, t, s, x) in cert["labels"] if r[k][t] == s and t < s}
        ok["labels"] = len(lab) == 3 * T // 2 == len(cert["labels"]) and all(isinstance(x, int) and x != 0 for x in lab.values())
        words = True
        for i in range(3):
            j, k = OTHER[i]; kind = kinds[i]
            for t in range(T):
                g, u, cur = ID, t, j
                for _ in range(2 * M[i]):
                    v = r[cur][u]; x = lab[(cur, min(u, v))]; e = x if u < v else -x
                    if kind == "U3": gen = U3X if cur == j else U3Y
                    else: gen = U4X if cur == kind[1] else U4Y
                    g = mmul(g, mpow(gen, e)); u = v; cur = k if cur == j else j
                words = words and g == ID
        ok["all vertex words = I over Z"] = words
        chi = nv - 3 * T // 2 + T
        bad = sorted(set().union(*[primes_of(x) for x in lab.values()]))
        good = all(ok.values()); allok = allok and good; count += 1
        print(fam, "T", T, "surface", cert["surface_index"], "orientable", ori, "chi", chi,
              "labels", sorted(set(lab.values())), "label primes", bad, ok, "PASS" if good else "FAIL")
print("certificates checked:", count, "|", "ALL PASS" if allok else "SOME FAIL")
