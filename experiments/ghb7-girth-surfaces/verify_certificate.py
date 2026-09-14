#!/usr/bin/env python3
"""Independent verifier for GHB_2(7) girth-surface certificates.  Shares no code with the search.

Checks, for every certificate:
  1. r0, r1, r2 are fixed-point-free involutions of {0..T-1}, and <r0,r1,r2> is transitive;
  2. <r1,r2>, <r0,r2>, <r0,r1> have every orbit of size exactly 6, 8, 8, and act freely there;
  3. the surface is orientable, and V - E + F = T/6 + T/8 + T/8 - 3T/2 + T;
  4. every label exponent lies in 1..6;
  5. for every chamber and vertex type, the word around the vertex is the identity of SL_4(F_7).
Also re-checks that psi(a), psi(b), psi(c) satisfy the eleven relators of G_{HB_2}(7).
usage: verify_certificate.py certificates-genus2.json
"""
import sys, json

P = 7
def mm(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(4)) % P for j in range(4)] for i in range(4)]
def ident():
    return [[int(i == j) for j in range(4)] for i in range(4)]
def unit(entries):
    M = ident()
    for (i, j, v) in entries: M[i][j] = (M[i][j] + v) % P
    return M
def pw(M, e):
    R = ident()
    for _ in range(e % 7): R = mm(R, M)
    return R
a = unit([(0, 3, 1), (1, 2, 1)]); b = unit([(1, 0, 1), (2, 3, -1)]); c = unit([(3, 1, 1)])
inv = lambda M: pw(M, 6)          # every generator has order 7; products are checked below
def comm(x, y):                    # [x,y] = x^-1 y^-1 x y, left-normed
    return mm(mm(invert(x), invert(y)), mm(x, y))
def invert(M):                     # exact inverse in SL_4(F_7) by adjugate-free search on powers
    R, Q = M, ident()
    for _ in range(343):
        if R == ident(): return Q
        Q = R; R = mm(R, M)
    raise ValueError("order > 343")
def lcomm(*xs):
    r = xs[0]
    for x in xs[1:]: r = comm(r, x)
    return r
I = ident()
rel = {"a^7": pw(a, 7) == I, "b^7": pw(b, 7) == I, "c^7": pw(c, 7) == I,
       "[a,b,a]": lcomm(a, b, a) == I, "[a,b,b]": lcomm(a, b, b) == I,
       "[c,b,c]": lcomm(c, b, c) == I, "[c,b,b,c]": lcomm(c, b, b, c) == I, "[c,b,b,b]": lcomm(c, b, b, b) == I,
       "[c,a,c]": lcomm(c, a, c) == I, "[c,a,a,c]": lcomm(c, a, a, c) == I, "[c,a,a,a]": lcomm(c, a, a, a) == I}
print("relators hold for psi(a),psi(b),psi(c):", all(rel.values()), rel if not all(rel.values()) else "")

GEN = [c, a, b]; PAIR = {0: (1, 2), 1: (0, 2), 2: (0, 1)}; HALF = {0: 3, 1: 4, 2: 4}
D = json.load(open(sys.argv[1])); allok = True
for cert in D["certificates"]:
    T = cert["T"]; r = [cert["r0"], cert["r1"], cert["r2"]]; ok = {}
    ok["involutions"] = all(len(rk) == T and all(rk[rk[t]] == t and rk[t] != t for t in range(T)) for rk in r)
    seen = {0}; st = [0]
    while st:
        u = st.pop()
        for k in range(3):
            if r[k][u] not in seen: seen.add(r[k][u]); st.append(r[k][u])
    ok["transitive"] = len(seen) == T
    orbit_ok, nverts = True, 0
    for i in range(3):
        j, k = PAIR[i]; done = set()
        for t in range(T):
            walk = [t]; cur = j
            while True:
                walk.append(r[cur][walk[-1]]); cur = k if cur == j else j
                if walk[-1] == t and len(walk) % 2 == 1: break
                if len(walk) > 4 * HALF[i] + 2: break
            if len(walk) - 1 != 2 * HALF[i] or len(set(walk[:-1])) != 2 * HALF[i]: orbit_ok = False
            if t not in done: nverts += 1; done.update(walk)
    ok["free orbits 6,8,8"] = orbit_ok
    col = {0: 0}; st = [0]; ori = True
    while st:
        u = st.pop()
        for k in range(3):
            v = r[k][u]
            if v not in col: col[v] = 1 - col[u]; st.append(v)
            elif col[v] == col[u]: ori = False
    ok["orientable"] = ori
    lab = {}
    for (k, t, s, x) in cert["labels"]:
        assert r[k][t] == s and t < s and (k, t) not in lab
        lab[(k, t)] = x
    ok["labels 1..6 on all 3T/2 edges"] = len(lab) == 3 * T // 2 and all(1 <= x <= 6 for x in lab.values())
    chi = nverts - 3 * T // 2 + T
    ok["chi"] = chi
    words_ok = True
    for i in range(3):
        j, k = PAIR[i]
        for t in range(T):
            g, u, cur = ident(), t, j
            for _ in range(2 * HALF[i]):
                v = r[cur][u]; x = lab[(cur, min(u, v))]
                g = mm(g, pw(GEN[cur], x if u < v else -x)); u = v; cur = k if cur == j else j
            if g != I: words_ok = False
    ok["all vertex words trivial"] = words_ok
    good = all(v for key, v in ok.items() if key != "chi") and chi == -2
    allok = allok and good
    print("surface", cert["surface_index"], ok, "genus", (2 - chi) // 2 if ori else None, "PASS" if good else "FAIL")
print("ALL PASS" if allok and all(rel.values()) else "SOME FAIL")
