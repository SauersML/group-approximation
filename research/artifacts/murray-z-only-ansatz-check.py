#!/usr/bin/env sage -python
"""Murray's z-only ansatz (arXiv:2106.02147) checked in the affine model of P.

  verify      u'u - 1 for u = p + q a + r b + s ab in ansatz form and Gardam's
              selection u' = x^-1 p_yz - x^-1 q a - y^-1 r b + z^-1 s_yz ab, in
              the group ring with f_i as symbols F_i and f_i^* as G_i. Compares
              the Q(z)-span of its coefficients and their *-images with
              Murray's six equations; checks Theorem 3 over GF(d), and over QQ.
  solve D F   all solutions over F (QQ or a prime) with f_1..f_7 supported in
              z^-D..z^D, from the group ring equations; progressive case split
              over the coefficients of f_1..f_6 (all zero is the trivial unit)
"""
import sys, time
from sage.all import PolynomialRing, LaurentPolynomialRing, QQ, GF, matrix
from sage.libs.singular.function_factory import singular_function
from cysignals.alarm import alarm, cancel_alarm, AlarmInterrupt

slimgb = singular_function("slimgb")
sdim = singular_function("dim")
vdim = singular_function("vdim")
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
REP = [ID, A, B, mul(A, B)]
SIG = [r[0] for r in REP]

def to_aff(c, e):  # x^i y^j z^k rep_c, with x, y, z = translations 2e1, 2e2, -2e3
    return mul((ID[0], (2 * e[0], 2 * e[1], -2 * e[2])), REP[c])

def from_aff(g):
    c = SIG.index(g[0])
    l = mul(g, inv(REP[c]))
    assert l[0] == ID[0] and all(t % 2 == 0 for t in l[1])
    return c, (l[1][0] // 2, l[1][1] // 2, -l[1][2] // 2)

assert to_aff(0, (1, 0, 0)) == mul(A, A) and to_aff(0, (0, 1, 0)) == mul(B, B)
assert to_aff(0, (0, 0, 1)) == mul(REP[3], REP[3])
assert mul(mul(inv(B), mul(A, A)), B) == inv(mul(A, A))
assert mul(mul(inv(A), mul(B, B)), A) == inv(mul(B, B))
assert from_aff(mul(B, A)) == (3, (-1, 1, -1)), "ba = x^-1 y z^-1 ab"

SWAP = None  # coefficient map under conjugation inverting z (verify mode)

def gr_mul(U, V):
    W = {}
    for (c, e), P in U.items():
        g = to_aff(c, e)
        for (d, f), Q in V.items():
            key = from_aff(mul(g, to_aff(d, f)))
            W[key] = W.get(key, 0) + P * (SWAP(Q) if SWAP and SIG[c][2] == -1 else Q)
    return {k: v for k, v in W.items() if v != 0}

def lat(*terms):
    W = {}
    for coef, e in terms:
        W[e] = W.get(e, 0) + coef
    return W

def lmul(*Ps):
    W = {(0, 0, 0): 1}
    for P in Ps:
        V = {}
        for e, a in W.items():
            for f, b in P.items():
                k = (e[0] + f[0], e[1] + f[1], e[2] + f[2])
                V[k] = V.get(k, 0) + a * b
        W = {k: v for k, v in V.items() if v != 0}
    return W

def lsum(*Ps):
    W = {}
    for P in Ps:
        for e, a in P.items():
            W[e] = W.get(e, 0) + a
    return {k: v for k, v in W.items() if v != 0}

def at(P, c, sign=1):
    return {(c, e): sign * v for e, v in P.items()}

def gsum(*Us):
    W = {}
    for U in Us:
        for k, a in U.items():
            W[k] = W.get(k, 0) + a
    return {k: v for k, v in W.items() if v != 0}

def mono(i, j, k):
    return {(i, j, k): 1}

def conj_a(P):  # a P a^-1 = P_yz on the lattice
    ai = from_aff(inv(A))
    W = gr_mul(gr_mul({(1, (0, 0, 0)): 1}, at(P, 0)), {ai: 1})
    assert all(c == 0 for c, _ in W)
    return {e: v for (_, e), v in W.items()}

def ansatz(f):
    one = mono(0, 0, 0)
    X, Xi, Y, Yi = mono(1, 0, 0), mono(-1, 0, 0), mono(0, 1, 0), mono(0, -1, 0)
    p = lmul(lsum(one, X), lsum(one, Y), f[1])
    q = lsum(lmul(lsum(one, X), lsum(Xi, Yi), f[2]), lmul(lsum(one, Yi), f[3]))
    r = lsum(lmul(lsum(one, Yi), lsum(X, Y), f[4]), lmul(lsum(one, X), f[5]))
    s = lsum(lmul(lsum(X, lat((4, (0, 0, 0))), Xi, Y, Yi), f[6]), f[7])
    u = gsum(at(p, 0), at(q, 1), at(r, 2), at(s, 3))
    up = gsum(at(lmul(Xi, conj_a(p)), 0), at(lmul(Xi, q), 1, -1),
              at(lmul(Yi, r), 2, -1), at(lmul(mono(0, 0, -1), conj_a(s)), 3))
    E = gr_mul(up, u)
    E[(0, (0, 0, 0))] = E.get((0, (0, 0, 0)), 0) - 1
    return {k: v for k, v in E.items() if v != 0}

mode = sys.argv[1]
if mode == "verify":
    names = [f"F{i}" for i in range(1, 8)] + [f"G{i}" for i in range(1, 8)]
    MR = LaurentPolynomialRing(QQ, names + ["z"])
    F, G, z = MR.gens()[:7], MR.gens()[7:14], MR.gens()[14]
    star = MR.hom(list(G) + list(F) + [z ** -1], MR)
    SWAP = lambda Q: star(MR(Q))
    f = {i: {(0, 0, 0): F[i - 1]} for i in range(1, 8)}
    E = ansatz(f)
    rows = {}
    for (c, (i, j, k)), v in E.items():
        rows[(c, i, j)] = rows.get((c, i, j), 0) + v * z ** k
    Erows = list(rows.values())
    stamp(f"u'u - 1: {len(E)} nonzero cells, {len(Erows)} (coset, x^i y^j) rows")
    f1, f2, f3, f4, f5, f6, f7 = F
    s1, s2, s3, s4, s5, s6, s7 = G
    M = [s7 * f7 - 1,
         s3 * f3 - s5 * f5, s3 * f3 - (s7 * f6 + s6 * f7) - 4 * s6 * f6,
         s2 * f2 - s4 * f4, s2 * f2 - s6 * f6,
         s1 * f1 - s2 * f3 - s4 * f5,
         s2 * f5 - z * s5 * f2, s2 * f5 - s3 * f4, s3 * f4 - z * s4 * f3,
         s2 * f5 - (s6 * f1 + z * s1 * f6) + (s2 * f4 + z * s4 * f2),
         s3 * f5 + z * s5 * f3 - (s7 * f1 + z * s1 * f7) - 4 * (s2 * f4 + z * s4 * f2)]
    Rz = PolynomialRing(QQ, "Z")
    Kz = Rz.fraction_field()
    Zg = Rz.gen()

    def vecs(exprs):
        out = []
        for ex in exprs:
            d = {}
            for ex2 in (ex, star(ex)):
                row = {}
                for mon, coef in ex2.dict().items():
                    mon = tuple(mon)
                    row[mon[:14]] = row.get(mon[:14], 0) + coef * Zg ** (mon[14] + 60)
                out.append(row)
        return out

    VE, VM = vecs(Erows), vecs(M)
    cols = sorted({k for row in VE + VM for k in row})
    def mat(V):
        return matrix(Kz, [[row.get(k, 0) for k in cols] for row in V])
    rE, rM, rEM = mat(VE).rank(), mat(VM).rank(), mat(VE + VM).rank()
    stamp(f"ranks over Q(z): coefficients {rE}, Murray {rM}, together {rEM}")
    stamp(f"Murray's equations follow from u'u = 1: {rEM == rE}; converse: {rEM == rM}")
    SWAP = None
    for d in (3, 5, 7, 0):
        Fd = GF(d) if d else QQ
        for t in (-1, 0, 1, 2):
            for w in (0, 1):
                dd = d if d else 3
                one = lat((Fd(1), (0, 0, 0)))
                h = one
                for _ in range(dd - 2):
                    h = lmul(h, lat((Fd(1), (0, 0, 0)), (Fd(-1), (0, 0, 1 - 2 * t))))
                c = lat((Fd(1), (0, 0, t)), (Fd(1), (0, 0, 1 - t)))
                fz = {1: lmul(c, h), 2: lmul(mono(0, 0, w), h),
                      3: lmul(mono(0, 0, w), lat((Fd(1), (0, 0, 0)), (Fd(1), (0, 0, 2 * t - 1))), h),
                      4: lmul(mono(0, 0, w + t), h), 5: lmul(mono(0, 0, w), c, h),
                      6: h, 7: lat((Fd(1), (0, 0, 2 * t - 1)))}
                E = ansatz(fz)
                stamp(f"Theorem 3 with h^(d-2), d = {dd}, over {Fd}, t = {t}, w = {w}: "
                      f"u'u = 1 is {not E}")
elif mode == "solve":
    D, Fs = int(sys.argv[2]), sys.argv[3]
    Fd = QQ if Fs == "QQ" else GF(int(Fs))
    names = [f"c{i}_{d + D}" for i in range(1, 8) for d in range(-D, D + 1)]
    R = PolynomialRing(Fd, names + ["w"], order="degrevlex")
    g = R.gens()
    idx = lambda i, d: (i - 1) * (2 * D + 1) + d + D
    f = {i: {(0, 0, d): g[idx(i, d)] for d in range(-D, D + 1)} for i in range(1, 8)}
    eqs = list(ansatz(f).values())
    stamp(f"D = {D} over {Fd}: {len(names)} unknowns, {len(eqs)} equations")
    nz = [idx(i, d) for i in range(1, 7) for d in range(-D, D + 1)]
    found = []
    for a, v in enumerate(nz):
        case = [g[b] for b in nz[:a]] + [g[v] * g[-1] - 1]
        try:
            alarm(7200)
            GB = slimgb(R.ideal(eqs + case))
            cancel_alarm()
        except AlarmInterrupt:
            stamp(f"case {names[v]} != 0: TIMEOUT")
            found.append((names[v], "timeout"))
            continue
        if any(p.is_constant() and p != 0 for p in GB):
            continue
        stamp(f"case {names[v]} != 0: nonempty, dim {sdim(GB)}, GB size {len(GB)}")
        found.append((names[v], len(GB)))
        if len(GB) < 60:
            print("\n".join(str(p) for p in GB), flush=True)
    stamp(f"D = {D} over {Fd}: nonempty cases {found}")
print("DONE", flush=True)
