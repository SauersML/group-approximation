# Core library for two-cell cores built from fiber products (lane w10-048, 2026-09-18).
# Letters: 0=x, 1=y, 2=X=x^-1, 3=Y=y^-1.  Abelianization x->t, y->s.  A Laurent polynomial is a
# dict {(i,j): coeff} meaning sum coeff * s^i t^j.
import itertools, random
from fractions import Fraction as Fr
LET = 'xyXY'
DV = {0: (0, 1), 1: (1, 0), 2: (0, -1), 3: (-1, 0)}


def inv(w): return [(l + 2) % 4 for l in reversed(w)]


def red(w):
    o = []
    for l in w:
        if o and (o[-1] - l) % 4 == 2: o.pop()
        else: o.append(l)
    return o


def pp(w):
    n = len(w); return any(n % d == 0 and w == w[:d] * (n // d) for d in range(1, n))


def mk(edges):
    tr = {}
    for i, (a, b, m) in enumerate(edges):
        tr[(a, m)] = (b, i, 1); tr[(b, m + 2)] = (a, i, -1)
    return tr


def read(tr, v, w, NE):
    z = [0] * NE
    for l in w:
        r = tr.get((v, l))
        if r is None: return None
        v, i, sg = r; z[i] += sg
    return v, z


def pinj(n):
    res = []
    for k in range(n + 1):
        for dom in itertools.combinations(range(n), k):
            for img in itertools.permutations(range(n), k):
                res.append(tuple(zip(dom, img)))
    return res


def canon(n, edges):
    best = None
    for p in itertools.permutations(range(n)):
        e = tuple(sorted((p[a], p[b], m) for a, b, m in edges))
        if best is None or e < best: best = e
    return best


def graphs(n, minrank=2, iso=True):
    P = pinj(n); seen = set()
    for X in P:
        for Y in P:
            edges = [(a, b, 0) for a, b in X] + [(a, b, 1) for a, b in Y]
            if len(edges) - n + 1 < minrank: continue
            deg = [0] * n
            for a, b, _ in edges: deg[a] += 1; deg[b] += 1
            if min(deg) < 2: continue
            ad = {i: set() for i in range(n)}
            for a, b, _ in edges: ad[a].add(b); ad[b].add(a)
            st = [0]; sn = {0}
            while st:
                u = st.pop()
                for v in ad[u]:
                    if v not in sn: sn.add(v); st.append(v)
            if len(sn) < n: continue
            if iso:
                c = canon(n, edges)
                if c in seen: continue
                seen.add(c); edges = list(c)
            yield edges


def comps(n, tr):
    """Off-diagonal components of Gamma x Gamma: list of (root, parent map, generator words)."""
    V = [(a, b) for a in range(n) for b in range(n) if a != b]
    seen = set(); out = []
    for r in V:
        if r in seen: continue
        par = {r: None}; q = [r]
        while q:
            u = q.pop()
            for l in range(4):
                ra = tr.get((u[0], l)); rb = tr.get((u[1], l))
                if ra and rb:
                    v = (ra[0], rb[0])
                    if v not in par: par[v] = (u, l); q.append(v)
        seen |= set(par)
        def tp(v):
            w = []
            while par[v] is not None:
                u, l = par[v]; w.append(l); v = u
            return w[::-1]
        gens = []
        for u in par:
            for l in (0, 1):
                ra = tr.get((u[0], l)); rb = tr.get((u[1], l))
                if not (ra and rb): continue
                v = (ra[0], rb[0])
                if par.get(v) == (u, l): continue
                gens.append(red(tp(u) + [l] + inv(tp(v))))
        out.append((r, par, gens))
    return out


def nullvecs(Z, NE, lam):
    """Integer vectors h with sum h_k (z1_k - lam z0_k) = 0 and sum h_k z0_k != 0 (a basis)."""
    import sympy as sp
    M = sp.Matrix([[z1[i] - lam * z0[i] for i in range(NE)] for z0, z1 in Z]).T
    out = []
    for h in M.nullspace():
        den = sp.ilcm(*[sp.fraction(x)[1] for x in h]); h = [int(x * den) for x in h]
        A = [sum(h[k] * Z[k][0][i] for k in range(len(Z))) for i in range(NE)]
        if any(A): out.append(h)
    return out


def build(tr, root, gens, h, tail):
    w = []
    for k, hk in enumerate(h):
        w += (gens[k] if hk > 0 else inv(gens[k])) * abs(hk)
    w = red(w + tail)
    a, b = root
    while len(w) > 1 and (w[0] - w[-1]) % 4 == 2:
        a = tr[(a, w[0])][0]; b = tr[(b, w[0])][0]; w = w[1:-1]
    return a, b, w


# ---- Laurent polynomials ----
def padd(p, q, c=1):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + c * v
        if r[k] == 0: del r[k]
    return r


def pmono(p, e):
    return {(k[0] + e[0], k[1] + e[1]): v for k, v in p.items()}


def tree_pot(tr, v0):
    pot = {v0: (0, 0)}; tree = set(); q = [v0]
    while q:
        u = q.pop()
        for l in range(4):
            r = tr.get((u, l))
            if r and r[0] not in pot:
                d = DV[l]; pot[r[0]] = (pot[u][0] + d[0], pot[u][1] + d[1]); tree.add(r[1]); q.append(r[0])
    return pot, tree


def crow_ab(edges, tr, v0, v1, w):
    """Abelianized cylinder row c_x = g d_x u0 - d_x u1 (eps = 1) in the spanning-tree basis from v0.
    Returns (basis edge indices, list of Laurent polys, exponent of g)."""
    pot, tree = tree_pot(tr, v0)
    basis = [i for i in range(len(edges)) if i not in tree]
    def fox(v):
        d = {i: {} for i in basis}; pre = pot[v]
        for l in w:
            v2, i, sg = tr[(v, l)]
            nxt = (pre[0] + DV[l][0], pre[1] + DV[l][1])
            if i in d:
                if sg == 1: d[i] = padd(d[i], {pre: 1})
                else: d[i] = padd(d[i], {nxt: 1}, -1)
            pre = nxt; v = v2
        return d
    d0 = fox(v0); d1 = fox(v1); g = pot[v1]
    c = [padd(pmono(d0[i], g), d1[i], -1) for i in basis]
    return basis, c, g


def ev_mod(p, sv, tv, q):
    r = 0
    for (i, j), c in p.items():
        r += c * pow(sv, i % (q - 1), q) * pow(tv, j % (q - 1), q)
    return r % q


def char_kill(c, primes=(2, 3, 5, 7, 11, 13)):
    for q in primes:
        for sv in range(1, q):
            for tv in range(1, q):
                if all(ev_mod(p, sv, tv, q) == 0 for p in c): return (q, sv, tv)
    return None


def to_sympy(c):
    import sympy as sp
    s, t = sp.symbols('s t')
    out = []
    for p in c:
        if not p: continue
        mi = min(k[0] for k in p); mj = min(k[1] for k in p)
        out.append(sp.expand(sum(v * s ** (k[0] - mi) * t ** (k[1] - mj) for k, v in p.items())))
    return out


def q_unit(c, modulus=None):
    """Do the entries of c generate the unit ideal of k[s^+-,t^+-] (k = Q, or F_p)?"""
    import sympy as sp
    s, t, z = sp.symbols('s t z')
    polys = to_sympy(c)
    if not polys: return False
    kw = {'modulus': modulus} if modulus else {}
    G = sp.groebner(polys + [z * s * t - 1], z, s, t, order='grevlex', **kw)
    return list(G.exprs) == [1]


def int_in_ideal(c):
    """A nonzero integer N in the ideal (c) of Z[s^+-,t^+-] via iterated resultants, or 0 if none found.
    Only primes dividing N can carry a character killing c (when q_unit(c) is True)."""
    import sympy as sp
    s, t = sp.symbols('s t')
    P = [p for p in to_sympy(c) if p != 0]
    def strip(f, x):
        f = sp.Poly(f, x)
        while f.degree() > 0 and f.eval(0) == 0: f = sp.Poly(sp.cancel(f.as_expr() / x), x)
        return f.as_expr()
    U = []
    for i in range(len(P)):
        for j in range(i + 1, len(P)):
            r = sp.resultant(P[i], P[j], t)
            if r != 0: U.append(strip(sp.expand(r), s))
        if len(U) >= 4: break
    N = 0
    for i in range(len(U)):
        for j in range(i + 1, len(U)):
            if sp.Poly(U[i], s).degree() == 0: r = U[i] ** 1
            elif sp.Poly(U[j], s).degree() == 0: r = U[j]
            else: r = sp.resultant(U[i], U[j], s)
            if r != 0: N = sp.igcd(N, int(r))
    return abs(int(N))


def z_unit(c):
    """True iff the entries of c generate Z[s^+-,t^+-] (no character over any field kills c).
    Returns (True/False/None, info)."""
    import sympy as sp
    if not q_unit(c): return False, 'Qbar'
    N = int_in_ideal(c)
    if N == 0: return None, 'noN'
    bad = [p for p in sp.primefactors(N) if not q_unit(c, modulus=p)]
    return (len(bad) == 0), bad
