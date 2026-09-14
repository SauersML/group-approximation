#!/usr/bin/env python3
"""Independent verifier: an integer-labelled girth surface for every G_{HB_2}(p), p an odd prime.

Shares no code with experiments/ghb7-girth-surfaces/.  For the certificate it checks:
  1. r0, r1, r2 are fixed-point-free involutions of {0..T-1} generating a transitive group;
  2. every alternating <r_j,r_k> walk closes after exactly 2*m_i distinct chambers, (m_0,m_1,m_2) = (3,4,4);
  3. the chamber graph is bipartite (orientable surface) and V - E + F = -2;
  4. every side carries exactly one label, a nonzero integer; the primes dividing some label are listed;
  5. every vertex word is the identity in the INTEGRAL vertex group, evaluated with explicit normal-form
     laws (no matrices):
       N3 = <a,b | [a,b,a], [a,b,b]>          elements b^beta a^alpha u^mu,        u = [a,b];
       N4 = <x,y | [x,y,x], [x,y,y,x], [x,y,y,y]> elements y^beta x^gamma u^mu v^nu, u = [x,y], v = [u,y],
     used for X_0 = <a,b> = N3, X_1 = <c,b> = N4(x=c, y=b), X_2 = <c,a> = N4(x=c, y=a);
  6. the same words evaluated through psi: a -> I+E03+E12, b -> I+E10-E23, c -> I+E31 over Z (cross-check);
  7. psi satisfies the eight commutator relators exactly over Z, and (psi(g)-I)^2 = 0 for g = a,b,c;
  8. the laws of 5 are group laws satisfying the relators (random associativity and relator tests);
  9. the symbolic psi-images of the normal forms of X_0, X_1, X_2 (printed; used for injectivity and
     intersections mod every odd prime in the proof node).
usage: verify_integer_certificate.py surface67-integer-labels.json
"""
import sys, json, random

HALF = {0: 3, 1: 4, 2: 4}
PAIR = {0: (1, 2), 1: (0, 2), 2: (0, 1)}

# ---------- 5. normal-form laws ----------
def n3_mul(g, h):                       # (beta, alpha, mu) = b^beta a^alpha u^mu
    return (g[0] + h[0], g[1] + h[1], g[2] + h[2] + g[1] * h[0])
def n4_mul(g, h):                       # (beta, gamma, mu, nu) = y^beta x^gamma u^mu v^nu
    b2 = h[0]
    return (g[0] + h[0], g[1] + h[1], g[2] + h[2] + b2 * g[1],
            g[3] + h[3] + g[1] * b2 * (b2 - 1) // 2 + b2 * g[2])
N3_ID, N4_ID = (0, 0, 0), (0, 0, 0, 0)
def n3_pow(g, e):
    r = N3_ID
    base = g if e >= 0 else n3_inv(g)
    for _ in range(abs(e)): r = n3_mul(r, base)
    return r
def n4_pow(g, e):
    r = N4_ID
    base = g if e >= 0 else n4_inv(g)
    for _ in range(abs(e)): r = n4_mul(r, base)
    return r
def n3_inv(g):
    b, a, m = g                         # solve g * h = id
    return (-b, -a, -m + a * b)
def n4_inv(g):
    b, c, m, n = g
    # h = (-b, -c, mu, nu) with g*h = id: mu = -m - (-b)*c = -m + b*c ; nu from the law
    mu = -m + b * c
    b2 = -b
    nu = -(n + c * b2 * (b2 - 1) // 2 + b2 * m)
    h = (-b, -c, mu, nu)
    assert n4_mul(g, h) == N4_ID and n4_mul(h, g) == N4_ID
    return h
def comm(mul, inv, x, y): return mul(mul(inv(x), inv(y)), mul(x, y))
def lcomm(mul, inv, *xs):
    r = xs[0]
    for x in xs[1:]: r = comm(mul, inv, r, x)
    return r

# 8. group laws and relators
random.seed(1)
for _ in range(2000):
    g, h, k = [tuple(random.randint(-5, 5) for _ in range(3)) for _ in range(3)]
    assert n3_mul(n3_mul(g, h), k) == n3_mul(g, n3_mul(h, k)) and n3_mul(g, n3_inv(g)) == N3_ID
    g, h, k = [tuple(random.randint(-5, 5) for _ in range(4)) for _ in range(3)]
    assert n4_mul(n4_mul(g, h), k) == n4_mul(g, n4_mul(h, k)) and n4_mul(g, n4_inv(g)) == N4_ID
A3, B3 = (0, 1, 0), (1, 0, 0)
X4, Y4 = (0, 1, 0, 0), (1, 0, 0, 0)
laws_ok = (lcomm(n3_mul, n3_inv, A3, B3, A3) == N3_ID and lcomm(n3_mul, n3_inv, A3, B3, B3) == N3_ID
           and lcomm(n3_mul, n3_inv, A3, B3) == (0, 0, 1)
           and lcomm(n4_mul, n4_inv, X4, Y4, X4) == N4_ID and lcomm(n4_mul, n4_inv, X4, Y4, Y4, X4) == N4_ID
           and lcomm(n4_mul, n4_inv, X4, Y4, Y4, Y4) == N4_ID
           and lcomm(n4_mul, n4_inv, X4, Y4) == (0, 0, 1, 0) and lcomm(n4_mul, n4_inv, X4, Y4, Y4) == (0, 0, 0, 1))
print("normal-form laws are associative, and satisfy the relators with u=[x,y], v=[u,y]:", laws_ok)

# generator of edge type k inside the vertex group of type i
def letter(i, k, e):
    if i == 0: return n3_pow(A3 if k == 1 else B3, e)          # X_0 = <a,b>: a = g_1, b = g_2
    return n4_pow(X4 if k == 0 else Y4, e)                     # X_1 = <c,b>, X_2 = <c,a>: c = g_0 is x
def vmul(i): return n3_mul if i == 0 else n4_mul
def vid(i): return N3_ID if i == 0 else N4_ID

# ---------- 6,7. psi over Z ----------
def mm(A, B): return tuple(tuple(sum(A[r][k] * B[k][c] for k in range(4)) for c in range(4)) for r in range(4))
I4 = tuple(tuple(int(r == c) for c in range(4)) for r in range(4))
def unip(entries):
    M = [list(r) for r in I4]
    for (r, c, v) in entries: M[r][c] += v
    return tuple(tuple(r) for r in M)
PA, PB, PC = unip([(0, 3, 1), (1, 2, 1)]), unip([(1, 0, 1), (2, 3, -1)]), unip([(3, 1, 1)])
def nil(M): return tuple(tuple(M[r][c] - int(r == c) for c in range(4)) for r in range(4))
def zero(M): return all(v == 0 for row in M for v in row)
sq_ok = all(zero(mm(nil(M), nil(M))) for M in (PA, PB, PC))
def mpow(M, e):                                               # valid because (M-I)^2 = 0
    N = nil(M); return tuple(tuple(int(r == c) + e * N[r][c] for c in range(4)) for r in range(4))
def minv(M): return mpow(M, -1)
def mcomm(x, y): return mm(mm(minv(x), minv(y)), mm(x, y))
def mlc(*xs):
    r = xs[0]
    for x in xs[1:]: r = mcomm(r, x)
    return r
rel_ok = all(mlc(*w) == I4 for w in [(PA, PB, PA), (PA, PB, PB), (PC, PB, PC), (PC, PB, PB, PC), (PC, PB, PB, PB),
                                     (PC, PA, PC), (PC, PA, PA, PC), (PC, PA, PA, PA)])
print("psi(a),psi(b),psi(c) satisfy the eight commutator relators over Z:", rel_ok, "| (psi(g)-I)^2 = 0:", sq_ok)
PGEN = {0: PC, 1: PA, 2: PB}

# ---------- 1-4. combinatorics ----------
D = json.load(open(sys.argv[1])); cert = D["certificate"]
T = cert["T"]; r = [cert["r0"], cert["r1"], cert["r2"]]; ok = {}
ok["fixed-point-free involutions"] = all(len(rk) == T and all(0 <= rk[t] < T and rk[t] != t and rk[rk[t]] == t for t in range(T)) for rk in r)
seen, st = {0}, [0]
while st:
    u = st.pop()
    for k in range(3):
        if r[k][u] not in seen: seen.add(r[k][u]); st.append(r[k][u])
ok["transitive"] = len(seen) == T
nvert = 0
orbits_ok = True
for i in range(3):
    j, k = PAIR[i]; covered = set()
    for t in range(T):
        walk, cur = [t], j
        for _ in range(2 * HALF[i]):
            walk.append(r[cur][walk[-1]]); cur = k if cur == j else j
        if walk[-1] != t or len(set(walk[:-1])) != 2 * HALF[i]: orbits_ok = False
        if t not in covered: nvert += 1; covered.update(walk)
ok["alternating walks close after exactly 6, 8, 8 distinct chambers"] = orbits_ok
colour, st, bip = {0: 0}, [0], True
while st:
    u = st.pop()
    for k in range(3):
        v = r[k][u]
        if v not in colour: colour[v] = 1 - colour[u]; st.append(v)
        elif colour[v] == colour[u]: bip = False
ok["orientable (bipartite chamber graph)"] = bip
chi = nvert - 3 * T // 2 + T
ok["V - E + F = -2"] = (chi == -2)
lab = {}
dup = False
for (k, t, s, x) in cert["labels"]:
    if (k, t) in lab or r[k][t] != s or not t < s: dup = True
    lab[(k, t)] = x
ok["one nonzero integer label per side"] = (not dup) and len(lab) == 3 * T // 2 and all(isinstance(x, int) and x != 0 for x in lab.values())
bad_primes = sorted({q for x in lab.values() for q in range(2, abs(x) + 1) if abs(x) % q == 0 and all(q % d for d in range(2, q))})
print("labels used:", sorted(set(lab.values())), "| primes dividing some label:", bad_primes)

# ---------- 5,6. vertex words ----------
words_nf, words_psi, total = 0, 0, 0
for i in range(3):
    j, k = PAIR[i]
    for t in range(T):
        g, M, u, cur = vid(i), I4, t, j
        for _ in range(2 * HALF[i]):
            v = r[cur][u]; x = lab[(cur, min(u, v))]; e = x if u < v else -x
            g = vmul(i)(g, letter(i, cur, e)); M = mm(M, mpow(PGEN[cur], e))
            u = v; cur = k if cur == j else j
        total += 1; words_nf += (g == vid(i)); words_psi += (M == I4)
ok["all vertex words trivial in N3/N4 over Z"] = (words_nf == total)
ok["all vertex words trivial through psi over Z"] = (words_psi == total)
for key, val in ok.items(): print(" ", key, ":", val)
print("vertices", nvert, "edges", 3 * T // 2, "faces", T, "chi", chi, "| words checked", total)

# ---------- 9. symbolic normal-form images ----------
def padd(p, q):
    out = dict(p)
    for key, val in q.items():
        out[key] = out.get(key, 0) + val
        if out[key] == 0: del out[key]
    return out
def pmul(p, q):
    out = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            key = tuple(a + b for a, b in zip(k1, k2)); out[key] = out.get(key, 0) + v1 * v2
            if out[key] == 0: del out[key]
    return out
def symmat(N, s):
    return [[padd({(0, 0, 0, 0): int(rr == cc)} if rr == cc else {}, {tuple(int(q == s) for q in range(4)): N[rr][cc]} if N[rr][cc] else {}) for cc in range(4)] for rr in range(4)]
def smm(A, B):
    return [[__import__("functools").reduce(padd, [pmul(A[rr][q], B[q][cc]) for q in range(4)], {}) for cc in range(4)] for rr in range(4)]
def fmt(p):
    names = "stuw"
    terms = []
    for key, val in sorted(p.items()):
        mon = "*".join(names[q] + ("^%d" % d if d > 1 else "") for q, d in enumerate(key) if d)
        terms.append(("%d" % val) + ("*" + mon if mon else ""))
    return " + ".join(terms)
cases = [("X_0=<a,b>: b^s a^t u^w, u=[a,b]", [nil(PB), nil(PA), nil(mcomm(PA, PB))]),
         ("X_1=<c,b>: b^s c^t u^w v^w', u=[c,b], v=[u,b]  (w' printed as 4th symbol)", [nil(PB), nil(PC), nil(mcomm(PC, PB)), nil(mcomm(mcomm(PC, PB), PB))]),
         ("X_2=<c,a>: a^s c^t u^w v^w', u=[c,a], v=[u,a]", [nil(PA), nil(PC), nil(mcomm(PC, PA)), nil(mcomm(mcomm(PC, PA), PA))])]
sym_ok = True
for name, Ns in cases:
    sym_ok = sym_ok and all(zero(mm(N, N)) for N in Ns)
    R = symmat(Ns[0], 0)
    for s, N in enumerate(Ns[1:], 1): R = smm(R, symmat(N, s))
    print("symbolic psi-image of", name)
    for rr in range(4):
        for cc in range(4):
            want = {(0, 0, 0, 0): 1} if rr == cc else {}
            if R[rr][cc] != want: print("   entry (%d,%d) = %s" % (rr, cc, fmt(R[rr][cc])))
print("commutator images square to zero:", sym_ok)
allok = laws_ok and rel_ok and sq_ok and sym_ok and all(ok.values())
print("ALL PASS" if allok else "SOME FAIL")
