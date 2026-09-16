# holonomy.py -- checks for sl2-root-triangle-2dim-iff-zero-frobenius-holonomy (2026-09-16).
# Pure python3, single-threaded.  Usage: python3 holonomy.py f trials seed
#   f = 3 (q = 8, F = F_64) or f = 4 (q = 16, F = F_256).
# (A) Sufficiency: for random semilinear gluings with zero Frobenius holonomy, the explicit
#     configuration of the artifact defines rho_i on generators that agree on every edge element.
# (B) Counts of relative-twist triples: all, semilinear, semilinear with zero holonomy.
# (C) Calibration of the necessity direction over K = F_{q^2} only (f = 3): for random semilinear
#     gluings, search all (sigma_1, sigma_2, sigma_3) and all normalized g_1, g_2 in SL_2(F) and report
#     whether a configuration exists; compare with the holonomy prediction.
import sys, random, itertools

f = int(sys.argv[1]); TRIALS = int(sys.argv[2]); random.seed(int(sys.argv[3]))
n = 2 * f; N = 1 << n; q = 1 << f
POLY = {6: 0b1000011, 8: 0b100011101}[n]      # x^6+x+1, x^8+x^4+x^3+x^2+1 (primitive)
EXP = [0] * (2 * N); LOG = [0] * N; x = 1
for i in range(N - 1):
    EXP[i] = x; LOG[x] = i; x <<= 1
    if x & N: x ^= POLY
assert x == 1
for i in range(N - 1, 2 * N): EXP[i] = EXP[i - (N - 1)]
def mul(a, b): return 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]
def inv(a): return EXP[(N - 1 - LOG[a]) % (N - 1)]
def pw(a, e): return 0 if a == 0 else EXP[(LOG[a] * e) % (N - 1)]
def sqrt(a): return pw(a, N // 2)
K8 = [y for y in range(N) if pw(y, q) == y]    # the subfield k = F_q inside F
assert len(K8) == q
s = EXP[1]; assert s not in K8                  # s = primitive element, not in k
def mm(A, B):
    return (mul(A[0], B[0]) ^ mul(A[1], B[2]), mul(A[0], B[1]) ^ mul(A[1], B[3]),
            mul(A[2], B[0]) ^ mul(A[3], B[2]), mul(A[2], B[1]) ^ mul(A[3], B[3]))
def minv(A):   # det 1 in char 2
    return (A[3], A[1], A[2], A[0])
def conj(g, A): return mm(mm(g, A), minv(g))
def U(y): return (1, y, 0, 1)
def V(y): return (1, 0, y, 1)
def D(t): return (t, 0, 0, inv(t))
def frob(A, b): return tuple(pw(a, 1 << b) for a in A)

# F_2-linear maps of k as 2^f-element lookup tables (dicts)
BASIS = []
for y in K8:   # choose an F_2-basis of k greedily
    span = {0}
    for b in BASIS:
        span |= {z ^ b for z in span}
    if y not in span: BASIS.append(y)
    if len(BASIS) == f: break
def lin_from_images(imgs):
    table = {0: 0}
    for mask in range(1, q):
        src = 0; dst = 0
        for i in range(f):
            if mask >> i & 1: src ^= BASIS[i]; dst ^= imgs[i]
        table[src] = dst
    return table
def random_gl():
    while True:
        imgs = [random.choice(K8) for _ in range(f)]
        t = lin_from_images(imgs)
        if len(set(t.values())) == q: return t
def compose(t2, t1): return {y: t2[t1[y]] for y in K8}
def semilinear(lam, a): return {y: mul(lam, pw(y, 1 << a)) for y in K8}
def inverse(t): return {v: k for k, v in t.items()}

def random_gluing(sem):
    """sem = list of (lam, a) for edges 12, 13, 23; returns alpha tables per (vertex, edge)."""
    al = {}
    for e, (i, j) in zip(("12", "13", "23"), ((1, 2), (1, 3), (2, 3))):
        lam, a = sem[e]
        ai = random_gl()
        al[(i, e)] = ai
        al[(j, e)] = compose(semilinear(lam, a), ai)      # phi_e = alpha_j alpha_i^{-1}
    return al
def iota(al, i, e, x):
    y = al[(i, e)][x]
    if (i, e) in ((1, "12"), (2, "12"), (3, "13")): return U(y)
    if (i, e) == (3, "23"): return V(mul(s, y))
    return V(y)
EDGES = (("12", 1, 2), ("13", 1, 3), ("23", 2, 3))
def agrees(rho, al):
    return all(rho[i](iota(al, i, e, x)) == rho[j](iota(al, j, e, x)) for e, i, j in EDGES for x in K8)

# (A) sufficiency construction
def construct(sem):
    (l12, a12), (l13, a13), (l23, a23) = sem["12"], sem["13"], sem["23"]
    assert (a12 + a23 - a13) % f == 0
    b1, b2, b3 = a13 % f, a23 % f, 0
    mu12 = pw(l12, 1 << b2); mu13 = l13; mu23 = mul(s, l23)
    g3 = D(sqrt(inv(mu13)))
    nu = mul(mu13, mu23)
    P = sqrt(mul(mu12, inv(nu)))
    h = (P, 1, 1, 0)
    g1 = h; g2 = mm(mm(h, U(inv(P))), D(sqrt(inv(mu12))))
    return {1: lambda M: conj(g1, frob(M, b1)), 2: lambda M: conj(g2, frob(M, b2)),
            3: lambda M: conj(g3, frob(M, b3))}
okA = 0
for t in range(TRIALS):
    a12, a23 = random.randrange(f), random.randrange(f)
    sem = {"12": (random.choice(K8[1:]), a12), "13": (random.choice(K8[1:]), (a12 + a23) % f),
           "23": (random.choice(K8[1:]), a23)}
    al = random_gluing(sem)
    okA += agrees(construct(sem), al)
print(f"(A) q={q}: zero-holonomy semilinear gluings with agreeing explicit configuration: {okA}/{TRIALS}")

# (B) counts
nGL = 1
for i in range(f): nGL *= (q - (1 << i))
nsem = f * (q - 1)
print(f"(B) q={q}: |GL_f(F_2)|^3 = {nGL**3}, semilinear triples = {nsem**3}, "
      f"zero holonomy = {(q-1)**3 * f**2}, nonzero holonomy semilinear = {nsem**3 - (q-1)**3 * f**2}")

# (C) necessity calibration over K = F only (f = 3 by default; slow for f = 4)
if f == 3 and TRIALS > 0:
    G1 = [(a, b, inv(b), 0) for a in range(N) for b in range(1, N)]        # g_1 e_2 in <e_1>
    G2 = [(p, 0, r, inv(p)) for p in range(1, N) for r in range(N)]        # g_2 e_2 in <e_2>
    def configs(al):
        found = 0
        for b3 in range(2 * f):
            for b1 in range(f):
                c1 = [g for g in G1 if all(conj(g, frob(iota(al, 1, "13", x), b1)) ==
                                           frob(iota(al, 3, "13", x), b3) for x in K8)]
                if not c1: continue
                for b2 in range(f):
                    c2 = [g for g in G2 if all(conj(g, frob(iota(al, 2, "23", x), b2)) ==
                                               frob(iota(al, 3, "23", x), b3) for x in K8)]
                    for g1 in c1:
                        for g2 in c2:
                            if all(conj(g1, frob(iota(al, 1, "12", x), b1)) ==
                                   conj(g2, frob(iota(al, 2, "12", x), b2)) for x in K8):
                                found += 1
        return found
    CT = max(1, TRIALS // 10)
    for t in range(CT):
        a = [random.randrange(f) for _ in range(3)]
        if t % 2 == 0: a[1] = (a[0] + a[2]) % f          # even trials: zero holonomy (control)
        sem ={"12": (random.choice(K8[1:]), a[0]), "13": (random.choice(K8[1:]), a[1]),
               "23": (random.choice(K8[1:]), a[2])}
        hol = (a[0] + a[2] - a[1]) % f
        cnt = configs(random_gluing(sem))
        print(f"(C) exponents (a12,a13,a23)={tuple(a)} holonomy={hol}: configurations over F with g_3 = I: {cnt}")
    # one non-semilinear gluing as well
    al = {}
    for e, (i, j) in zip(("12", "13", "23"), ((1, 2), (1, 3), (2, 3))):
        ai = random_gl(); al[(i, e)] = ai
        while True:
            phi = random_gl()
            if not any(phi == semilinear(l, b) for l in K8[1:] for b in range(f)): break
        al[(j, e)] = compose(phi, ai) if e == "12" else compose(semilinear(1, 0), ai)
    print(f"(C) non-semilinear twist on E_12 only, identity elsewhere: configurations over F: {configs(al)}")
