# lx-review round 3b: consistency of OddPTotal.EvenReducedPowers on a model where it is genuine.
# Model: A = F_p[h1,h2]/(h1^(M+1), h2^(M+1)) (cohomology of CP^M x CP^M), degrees deg h = 2.
# Raw total power: the ring endomorphism Ptot with Ptot(h) = mu*h + h^p (mu = -1), i.e. [D_{2(p-1)} h] = mu h, [D_0 h] = h^p.
# Packaged: on a homogeneous class of degree 2k, P^i := mu^{-(k-i)} * projDeg_{2k+2i(p-1)}(Ptot x) if i <= k, else 0; extended additively.
# Predicates checked exactly (dict polynomials over F_p):
#  zero_one:   P^0 1 = 1, P^n 1 = 0 (n>0)
#  zero_cp:    P^0 h = h on degree-2 classes (all degree-2 classes of the model are Euler classes)
#  degree_two: P^1 h = h^p;  P^j h = 0 for j >= 2
#  unstable:   P^i x = 0 when deg x < 2i
#  cartan:     P^i(u v) = sum_j P^j u P^{i-j} v, for all monomials u, v (all classes junk-free here)
#  mul_single: for z = h1*h2 - h2^2 (homogeneous, Ptot z = nu z?) -> check only when Ptot z is a multiple of z,
#              then P^i(z w) = c z P^i w with c independent of i, w (monomials w)
import itertools, random
def run(p, M):
    mu = p - 1
    inv = lambda x: pow(x % p, p - 2, p)
    def mul(a, b):
        out = {}
        for (e1, c1) in a.items():
            for (e2, c2) in b.items():
                e = (e1[0] + e2[0], e1[1] + e2[1])
                if e[0] > M or e[1] > M: continue
                out[e] = (out.get(e, 0) + c1 * c2) % p
        return {e: c for e, c in out.items() if c}
    def add(a, b, s=1):
        out = dict(a)
        for e, c in b.items(): out[e] = (out.get(e, 0) + s * c) % p
        return {e: c for e, c in out.items() if c}
    def smul(s, a): return {e: (s * c) % p for e, c in a.items() if (s * c) % p}
    def powr(a, k):
        r = {(0, 0): 1}
        for _ in range(k): r = mul(r, a)
        return r
    one = {(0, 0): 1}
    h1 = {(1, 0): 1}; h2 = {(0, 1): 1}
    P1 = add(smul(mu, h1), powr(h1, p)); P2 = add(smul(mu, h2), powr(h2, p))
    def ptot(x):
        out = {}
        for (a, b), c in x.items():
            out = add(out, smul(c, mul(powr(P1, a), powr(P2, b))))
        return out
    def proj(x, d): return {e: c for e, c in x.items() if 2 * (e[0] + e[1]) == d}
    def Pi(i, x):
        out = {}
        for d in set(2 * (e[0] + e[1]) for e in x):
            xd = proj(x, d); k = d // 2
            if i <= k:
                out = add(out, smul(pow(inv(mu), k - i, p), proj(ptot(xd), d + 2 * i * (p - 1))))
        return out
    checks = fails = 0
    def chk(b):
        nonlocal checks, fails
        checks += 1; fails += (not b)
    chk(Pi(0, one) == one)
    for n in range(1, 4): chk(Pi(n, one) == {})
    for a in range(p):
        for b in range(p):
            h = add(smul(a, h1), smul(b, h2))
            chk(Pi(0, h) == h); chk(Pi(1, h) == powr(h, p))
            for j in range(2, 5): chk(Pi(j, h) == {})
    mons = [{(a, b): 1} for a in range(M + 1) for b in range(M + 1)]
    for x in mons:
        (a, b), = x.keys(); k = a + b
        for i in range(k + 1, k + 4): chk(Pi(i, x) == {})
    random.seed(p * 1000 + M)
    for _ in range(300):
        u = random.choice(mons); v = random.choice(mons)
        for i in range(0, 5):
            lhs = Pi(i, mul(u, v)); rhs = {}
            for j in range(i + 1): rhs = add(rhs, mul(Pi(j, u), Pi(i - j, v)))
            chk(lhs == rhs)
    # mul_single at a single-component class: z = h1^M h2^M (top class; Ptot z = mu^(2M) z + higher = mu^(2M) z)
    z = {(M, M): 1}
    pz = ptot(z)
    nu = pz.get((M, M), 0)
    chk(pz == smul(nu, z))
    cs = set()
    for w in mons + [one]:
        for i in range(0, 4):
            lhs = Pi(i, mul(z, w)); pw = Pi(i, w); rhs = mul(z, pw)
            if rhs:
                # find c with lhs = c * rhs
                e0 = next(iter(rhs)); c = (lhs.get(e0, 0) * inv(rhs[e0])) % p
                chk(lhs == smul(c, rhs)); cs.add(c)
            else:
                chk(lhs == {})
    chk(len(cs) <= 1)
    return checks, fails
T = F = 0
for p in (3, 5, 7):
    for M in (p, 2 * p + 1):
        c, f = run(p, M); T += c; F += f
        print("p", p, "M", M, "checks", c, "fails", f)
print("TOTAL checks", T, "failures", F)
