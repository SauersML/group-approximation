#!/usr/bin/env python3
"""Checks for s-arithmetic-affine-rn-groups-are-k-graph-full-groups-proof.

K = F_q(t) (q prime), v = (t), S' = {inf, p_1..p_{k-1}}, U = <t, p_1..p_{k-1}>.
P_n = { x -> (t^m x + N)/Q : Q = prod p_i^{n_i}, m = n_inf + sum n_i deg p_i, deg N < m }.
An element is stored as (m, e, N): x -> (t^m x + N)/Q_e with e = (n_1..n_{k-1}); so d = (m - sum e_i deg p_i, e).
A. |P_n| = q^m and a -> a(O) (N/Q mod t^m) is a bijection onto balls of depth m.
B. For all colours i, j: E_i x E_j -> P_{e_i+e_j}, (x, y) -> xy is a bijection (k-graph factorisation).
C. Unique factorisation: brute force for small degrees, explicit solver for random larger ones.
D. Germ step: g in Aff(R, U), mu in P_(M,..,M) with g mu(O) in O  ==>  g mu in P, for M >= M0(g).
E. Koszul homology of the one-vertex k-graph over Z (Smith form) = (Z/(q-1))^C(k-1,j).
F. Number fields: trivial characters u -> |u|_v prod_{s in I} s(u) on U (rational homology criterion).
"""
import itertools, random
from math import comb
from sympy import Matrix, ZZ, sqrt, Rational, simplify, nsimplify
from sympy.matrices.normalforms import smith_normal_form

def trim(a):
    a = list(a)
    while a and a[-1] == 0: a.pop()
    return tuple(a)
def add(a, b, q):
    n = max(len(a), len(b)); return trim([((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % q for i in range(n)])
def mul(a, b, q):
    if not a or not b: return ()
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] = (r[i + j] + x * y) % q
    return trim(r)
def neg(a, q): return trim([(-x) % q for x in a])
def deg(a): return len(a) - 1 if a else -1
def tpow(m): return tuple([0] * m + [1])
def ppow(ps, e, q):
    r = (1,)
    for p, k in zip(ps, e):
        for _ in range(k): r = mul(r, p, q)
    return r
def series(N, Q, m, q):
    """first m coefficients of N/Q in F_q[[t]] (Q(0) != 0)."""
    inv0 = pow(Q[0], q - 2, q); c = []; rem = list(N) + [0] * m
    for i in range(m):
        x = (rem[i] * inv0) % q if i < len(rem) else 0; c.append(x)
        for j, y in enumerate(Q):
            if i + j < len(rem): rem[i + j] = (rem[i + j] - x * y) % q
    return tuple(c)
def polys(q, n): return [trim(c) for c in itertools.product(range(q), repeat=n)]

class Setup:
    def __init__(s, q, ps):
        s.q, s.ps, s.k = q, ps, len(ps) + 1; s.dg = [deg(p) for p in ps]
    def m_of(s, n): return n[0] + sum(a * b for a, b in zip(n[1:], s.dg))
    def P(s, n):
        m = s.m_of(n); return [(m, tuple(n[1:]), N) for N in polys(s.q, m)]
    def compose(s, a, b):  # a o b ; a = (m1,e1,N1), b = (m2,e2,N2)
        (m1, e1, N1), (m2, e2, N2) = a, b; q = s.q
        N = add(mul(tpow(m1), N2, q), mul(N1, ppow(s.ps, e2, q), q), q)
        return (m1 + m2, tuple(x + y for x, y in zip(e1, e2)), N)
    def inP(s, a):
        m, e, N = a; return m >= 0 and all(x >= 0 for x in e) and m - sum(x * y for x, y in zip(e, s.dg)) >= 0 and deg(N) < m
    def deg_of(s, a): m, e, _ = a; return (m - sum(x * y for x, y in zip(e, s.dg)),) + tuple(e)
    def split(s, a, p):  # solve a = a' a'' with d(a') = p
        m, e, N = a; q = s.q; m1 = s.m_of(p); e1 = tuple(p[1:]); e2 = tuple(x - y for x, y in zip(e, e1))
        Q2 = ppow(s.ps, e2, q)
        N1 = trim(series(N, Q2, m1, q))
        R = add(N, neg(mul(N1, Q2, q), q), q)
        assert all(x == 0 for x in R[:m1]); N2 = trim(R[m1:])
        return (m1, e1, N1), (m - m1, e2, N2)

def unit(k, i): return tuple(1 if j == i else 0 for j in range(k))
def run(q, ps, box, rnd):
    S = Setup(q, ps); k = S.k; name = f'q={q}, p_i={ps}'
    for n in itertools.product(range(box + 1), repeat=k):
        Pn = S.P(n); m = S.m_of(n)
        assert len(Pn) == q ** m and all(S.inP(a) and S.deg_of(a) == n for a in Pn)
        balls = {series(N, ppow(ps, e, q), m, q) for (_, e, N) in Pn}; assert len(balls) == q ** m
    E = [S.P(unit(k, i)) for i in range(k)]
    for i in range(k):
        for j in range(k):
            tgt = set(S.P(tuple(a + b for a, b in zip(unit(k, i), unit(k, j)))))
            prods = [S.compose(x, y) for x in E[i] for y in E[j]]
            assert len(set(prods)) == len(prods) == len(tgt) and set(prods) == tgt
    nb = 0
    for p in itertools.product(range(2), repeat=k):
        for r in itertools.product(range(2), repeat=k):
            pr = tuple(a + b for a, b in zip(p, r)); A, B = S.P(p), S.P(r)
            cnt = {}
            for x in A:
                for y in B:
                    z = S.compose(x, y); cnt[z] = cnt.get(z, 0) + 1
            assert set(cnt) == set(S.P(pr)) and set(cnt.values()) == {1}; nb += 1
    random.seed(1)
    for _ in range(rnd):
        n = tuple(random.randint(0, 5) for _ in range(k)); p = tuple(random.randint(0, x) for x in n)
        m = S.m_of(n); a = (m, tuple(n[1:]), trim([random.randrange(q) for _ in range(m)]))
        x, y = S.split(a, p); assert S.inP(x) and S.inP(y) and S.deg_of(x) == p and S.compose(x, y) == a
    # D. g(x) = u x + b, u = t^a0 prod p_i^ai, b = B / (t^c0 prod p_i^ci);  mu(x) = (t^m x + N)/Q_M,  Q_M = prod p_i^M.
    # g mu has multiplier t^(m+a0) / Q', Q' = prod p_i^(M-ai), and translation c = N'/Q', N' = t^a0 N + b Q'.
    # Predicted threshold: M >= M0(g) = max_i(ai + ci, -a0 - sum ai di, deg B - c0 - sum ci di - a0 - sum ai di + 1).
    hits = viol = 0; worst = 0
    for _ in range(40):
        a0 = random.randint(-3, 3); ai = [random.randint(-2, 2) for _ in ps]; ci = [random.randint(0, 2) for _ in ps]
        c0 = random.randint(0, 2); B = trim([random.randrange(q) for _ in range(random.randint(0, 6))])
        sd = sum(x * y for x, y in zip(ai, S.dg)); degb = deg(B) - c0 - sum(x * y for x, y in zip(ci, S.dg))
        M0 = max([x + y for x, y in zip(ai, ci)] + [-a0 - sd, degb - a0 - sd + 1, 0])
        worst = max(worst, M0)
        for M in range(M0, M0 + 4):
            m = S.m_of(tuple([M] * k)); s = max(c0, -a0, 0)
            for _ in range(60):
                N = trim([random.randrange(q) for _ in range(m)])
                e2 = [M - x - y for x, y in zip(ai, ci)]
                T = add(mul(tpow(s + a0), N, q), mul(mul(tpow(s - c0), B, q), ppow(ps, e2, q), q), q)  # t^s N'
                if m + a0 < 0 or any(T[i] for i in range(min(s, len(T)))): continue  # g mu(O) not in O
                hits += 1; Np = trim(T[s:]); ep = tuple(M - x for x in ai)
                gm = (m + a0, ep, Np)
                if not S.inP(gm): viol += 1
    assert viol == 0 and hits > 0
    M0 = f'formula (worst {worst}); {hits} germ tests with g mu(O) in O, all g mu in P'
    print(f'{name}: k={k}; |P_n| = q^m and ball bijection for n in [0,{box}]^k; factorisation bijections '
          f'E_i x E_j -> P for all i,j; brute-force uniqueness on {nb} degree pairs; {rnd} random splits OK; germ step: {M0}')
    a = [1 - q] + [1 - q ** d for d in S.dg]
    return a

def koszul(a):
    k = len(a); ranks = []
    subsets = {j: list(itertools.combinations(range(k), j)) for j in range(k + 1)}
    def dmat(j):  # C_j -> C_{j-1}
        M = [[0] * len(subsets[j]) for _ in subsets[j - 1]]
        for c, I in enumerate(subsets[j]):
            for pos, i in enumerate(I):
                J = I[:pos] + I[pos + 1:]; M[subsets[j - 1].index(J)][c] += (-1) ** pos * a[i]
        return Matrix(M)
    H = []
    for j in range(k + 1):
        kerdim = len(subsets[j]) - (dmat(j).rank() if j > 0 else 0)
        if j < k:
            D = dmat(j + 1); snf = smith_normal_form(D, domain=ZZ); inv = [abs(snf[i, i]) for i in range(min(snf.shape)) if snf[i, i] != 0]
        else:
            inv = []
        free = kerdim - len(inv); H.append((free, sorted(x for x in inv if x != 1)))
    return H

if __name__ == '__main__':
    cfg = [(2, [(1, 1)], 3, 300), (3, [(1, 1)], 2, 200), (2, [(1, 1), (1, 1, 1)], 2, 200), (3, [(1, 1), (1, 0, 1)], 1, 150),
           (2, [(1, 1), (1, 1, 1), (1, 1, 0, 1)], 1, 100)]
    print('== A-D. one-vertex k-graph monoids P in Aff(R, U)')
    for q, ps, box, rnd in cfg:
        a = run(q, ps, box, rnd)
        H = koszul(a); k = len(a)
        exp = [(0, [q - 1] * comb(k - 1, j) if q > 2 else []) for j in range(k)] + [(0, [])]
        print(f'   E. Koszul on {a}: H_j = {H}  expected (Z/{q-1})^C({k-1},j)')
        assert H == exp
    print('== F. number fields: characters u -> |u|_v prod_{s in I} s(u), trivial on U?')
    ex = [('Q, v=2, U=<2> (odometer)', [(Rational(1, 2), [2])]),
          ('Q, v=2, U=<2,3> (BS(1,3))', [(Rational(1, 2), [2]), (1, [3])]),
          ('Q, v=3, U=<3,2>', [(Rational(1, 3), [3]), (1, [2])]),
          ('Q(sqrt2), v=(sqrt2), U=<sqrt2, 1+sqrt2>', [(Rational(1, 2), [sqrt(2), -sqrt(2)]), (1, [1 + sqrt(2), 1 - sqrt(2)])])]
    for name, gens in ex:
        n = len(gens[0][1]); triv = []
        for j in range(n + 1):
            for I in itertools.combinations(range(n), j):
                if all(simplify(av * __import__('sympy').prod([emb[i] for i in I]) - 1) == 0 for av, emb in gens): triv.append(I)
        print(f'   {name}: trivial characters for I in {triv} -> rationally acyclic: {not triv}')
    print('ALL OK')
