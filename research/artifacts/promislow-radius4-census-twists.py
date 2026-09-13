#!/usr/bin/env sage -python
"""Structure of the 16 points of case (0,1) for the seven representatives in
census_pairs.json.

P^ab = Z/4 + Z/4 on a, b. For (p, q) in (Z/4)^2 let chi(g) = i^(p A(g) + q B(g)),
where (A(g), B(g)) is the image of g in P^ab. If chi is multiplicative on
S x T, then u -> sum chi(g) u_g g, v -> sum chi(h) v_h h sends a solution of
u v = 1 on (S, T) to another one. After rescaling so that u_0 = 1 it is again
a point of I_01. The script recomputes the 16 points as census_verify.py does,
then checks:
1. chi is multiplicative on (S u T) x (S u T), and ab(a) = (1,0), ab(b) = (0,1);
2. the 16 twists of one point are pairwise distinct and are exactly the 16 points;
3. for j = 3, 5, 7, the Galois conjugate zeta_8 -> zeta_8^j of that point is
   the twist by some (p, q), printed.
It also prints the coefficients u_g of that point.
"""
import json, time, random
from sage.all import PolynomialRing, QQ, CyclotomicField, matrix, vector
from sage.libs.singular.function_factory import singular_function

slimgb = singular_function("slimgb")
kbase = singular_function("kbase")
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

def el(p):
    return (tuple(p[0]), tuple(p[1]))

A = ((1, -1, -1), (1, 1, 0))
B = ((-1, 1, -1), (0, 1, 1))
REPS = [ID, A, B, mul(A, B)]
SIGNS = [r[0] for r in REPS]

def ab(g):
    """g = r_i x^e0 y^e1 z^e2 with x = a^2, y = b^2, z = (ab)^2 -> (A, B) in (Z/4)^2."""
    i = SIGNS.index(g[0])
    n = mul(inv(REPS[i]), g)
    assert n[0] == (1, 1, 1) and all(t % 2 == 0 for t in n[1])
    e0, e1, e2 = n[1][0] // 2, n[1][1] // 2, -n[1][2] // 2
    return (int(i in (1, 3)) + 2 * e0 + 2 * e2) % 4, (int(i in (2, 3)) + 2 * e1 + 2 * e2) % 4

assert ab(A) == (1, 0) and ab(B) == (0, 1) and ab(ID) == (0, 0)

def quotient(R, eqs, seed):
    G = slimgb(R.ideal([e for e in eqs if e != 0]))
    assert sdim(G) == 0
    GL, Bs = list(G), list(kbase(G))
    idx = {b: i for i, b in enumerate(Bs)}
    def nf(p):
        r, vec = p.reduce(GL), [QQ(0)] * len(Bs)
        for c, mon in zip(r.coefficients(), r.monomials()):
            vec[idx[mon]] = c
        return vector(QQ, vec)
    random.seed(seed)
    L = sum(random.randint(-9, 9) * x for x in R.gens())
    M = matrix(QQ, [nf(L * b) for b in Bs])
    return Bs, nf, M

def table(S, T, ring, u, v):
    eqs = {}
    for a in range(len(S)):
        for b in range(len(T)):
            c = mul(S[a], T[b])
            eqs[c] = eqs.get(c, ring(0)) + u[a] * v[b]
    return eqs

K8 = CyclotomicField(8)
z8 = K8.gen()
I4 = z8 ** 2
sig = {j: K8.hom([z8 ** j]) for j in (3, 5, 7)}

def twist(uu, vv, S, T, p, q):
    cu = [I4 ** ((p * ab(s)[0] + q * ab(s)[1]) % 4) for s in S]
    cv = [I4 ** ((p * ab(t)[0] + q * ab(t)[1]) % 4) for t in T]
    lam = cu[0] * uu[0]
    return tuple([c * x / lam for c, x in zip(cu, uu)] + [c * x * lam for c, x in zip(cv, vv)])

for k, d in enumerate(json.load(open("census_pairs.json"))):
    S, T = [el(p) for p in d["S"]], [el(p) for p in d["T"]]
    n, m = len(S), len(T)
    E = S + T
    ok_chi = all(tuple((x + y) % 4 for x, y in zip(ab(g), ab(h))) == ab(mul(g, h)) for g in E for h in E)
    R = PolynomialRing(QQ, [f"u{i}" for i in range(1, n)] + [f"v{j}" for j in range(m)] + ["w"],
                       order="degrevlex")
    g = R.gens()
    u, v = [R(1)] + list(g[:n - 1]), g[n - 1:n - 1 + m]
    eqs = table(S, T, R, u, v)
    eqs[ID] -= 1
    Bs, nf, M = quotient(R, list(eqs.values()) + [u[1] * g[-1] - 1], k)
    cp, N = M.charpoly(), len(Bs)
    assert cp.is_squarefree() and cp.degree() == N == 16
    rows = [nf(R(1))]
    for _ in range(N - 1):
        rows.append(rows[-1] * M)
    Amat = matrix(QQ, rows)
    H = {x: Amat.solve_left(nf(x)) for x in g}
    roots = [r for r, _ in cp.change_ring(K8).roots()]
    assert len(roots) == N
    pts = []
    for th in roots:
        P = {x: sum(H[x][i] * th ** i for i in range(N)) for x in g}
        uu, vv = [K8(1)] + [P[x] for x in g[:n - 1]], [P[x] for x in v]
        acc = table(S, T, K8, uu, vv)
        assert all(val == (1 if c == ID else 0) for c, val in acc.items())
        pts.append(tuple(uu + list(vv)))
    base = pts[0]
    tw = {(p, q): twist(base[:n], base[n:], S, T, p, q) for p in range(4) for q in range(4)}
    ok_orbit = len(set(tw.values())) == 16 and set(tw.values()) == set(pts)
    gal = {}
    for j in (3, 5, 7):
        conj = tuple(sig[j](x) for x in base)
        gal[j] = [pq for pq, t in tw.items() if t == conj]
    stamp(f"orbit {k}: chi multiplicative on (S u T)^2 {ok_chi}, 16 twists distinct and equal to "
          f"the 16 points {ok_orbit}, Galois j -> twists (p,q) {gal}")
    stamp(f"orbit {k}: u of one point: {[str(x) for x in base[:n]]}")
print("DONE", flush=True)
