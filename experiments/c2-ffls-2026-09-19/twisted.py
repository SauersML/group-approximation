"""Twisted Alexander torsion of H = <b,c,d,e | r> under rho x eps, rho: H -> S_n transitive.

Lemma M (see the -proof node): if H has an FFLS then for every finite-index H' <= H the
Q[t^+-1]-torsion of H_1(H' cap ker eps; Q) has an order all of whose primitive integral factors
are bi-monic (leading and constant coefficient +-1).  By Shapiro this order is the torsion order
of H_1(H; Q[t^+-1] (x) Q^n_rho), i.e. the gcd of the maximal-rank minors of the twisted Fox matrix.

Usage: python3 twisted.py N [MAXREPS]
"""
import sys, itertools, random
from flint import fmpz_poly, fmpz_mat, fmpq_poly, fmpq
R = 'eDDEdd' + 'bCB' + 'eDDEdd' + 'bDcBd'
EPS = {'b': 3, 'c': 0, 'd': 1, 'e': 1}
GENS = 'bcde'

def mul(g, h):                       # (g*h)(i) = g(h(i)); matches P(g)P(h), P(g)e_i = e_{g(i)}
    return tuple(g[x] for x in h)
def inv(g):
    r = [0] * len(g)
    for i, x in enumerate(g): r[x] = i
    return tuple(r)
def word(w, im):
    n = len(next(iter(im.values())))
    g = tuple(range(n))
    for ch in w:
        x = im[ch.lower()]
        g = mul(g, x if ch.islower() else inv(x))
    return g
def cycles(g):
    seen, out = set(), []
    for i in range(len(g)):
        if i in seen: continue
        c, j = [], i
        while j not in seen: seen.add(j); c.append(j); j = g[j]
        out.append(c)
    return out
def conjugator(u, w):                # some g with g u g^-1 = w, or None
    cu = sorted(cycles(u), key=len); cw = sorted(cycles(w), key=len)
    if [len(c) for c in cu] != [len(c) for c in cw]: return None
    g = [0] * len(u)
    for a, b in zip(cu, cw):
        for x, y in zip(a, b): g[x] = y
    return tuple(g)
def centralizer(u):
    n = len(u)
    return [g for g in itertools.permutations(range(n)) if mul(mul(g, u), inv(g)) == u]
def transitive(gs):
    n = len(gs[0]); seen = {0}; st = [0]
    while st:
        i = st.pop()
        for g in gs:
            for j in (g[i], inv(g)[i]):
                if j not in seen: seen.add(j); st.append(j)
    return len(seen) == n

def reps(n):
    """All transitive (b,c,d,e) with r = 1, b ranging over cycle-type representatives."""
    types = set()
    for g in itertools.permutations(range(n)):
        types.add(tuple(sorted(len(c) for c in cycles(g))))
    bs = []
    for tp in sorted(types):
        g, k = [0] * n, 0
        for L in tp:
            for i in range(L): g[k + i] = k + (i + 1) % L
            k += L
        bs.append(tuple(g))
    allp = list(itertools.permutations(range(n)))
    for b in bs:
        for d in allp:
            for e in allp:
                im = {'b': b, 'd': d, 'e': e}
                z = word('eDDEdd', im); beta = word('bDB', im)
                u = mul(z, beta); w = inv(mul(d, z))
                g0 = conjugator(u, w)
                if g0 is None: continue
                for cen in centralizer(u):
                    cp = mul(g0, cen)
                    c = mul(mul(inv(b), inv(cp)), b)
                    im2 = dict(im, c=c)
                    if not transitive([b, c, d, e]): continue
                    assert word(R, im2) == tuple(range(n))
                    yield im2

def fox(im, n):
    """Blocks J_g (g in GENS) as dict exp -> n x n int matrix (list of lists)."""
    J = {g: {} for g in GENS}
    pre, pe = tuple(range(n)), 0
    def add(g, perm, ex, sgn):
        M = J[g].setdefault(ex, [[0] * n for _ in range(n)])
        for i in range(n): M[perm[i]][i] += sgn          # P(perm) e_i = e_{perm(i)}
    for ch in R:
        l = ch.lower(); x = im[l]
        if ch.islower():
            add(l, pre, pe, 1); pre = mul(pre, x); pe += EPS[l]
        else:
            pre = mul(pre, inv(x)); pe -= EPS[l]; add(l, pre, pe, -1)
    return J

def polymat(J, n):
    """n x 4n matrix of fmpz_poly, shifted to nonnegative exponents."""
    m = min(ex for g in GENS for ex in J[g])
    P = [[fmpz_poly(0) for _ in range(4 * n)] for _ in range(n)]
    for k, g in enumerate(GENS):
        for ex, M in J[g].items():
            mono = fmpz_poly([0] * (ex - m) + [1])
            for i in range(n):
                for j in range(n):
                    if M[i][j]: P[i][k * n + j] += M[i][j] * mono
    return P

def evalmat(P, x):
    return fmpz_mat([[int(p(x)) for p in row] for row in P])

def interp(xs, ys):
    """Newton interpolation over Q, returns fmpq_poly."""
    c = [fmpq(y) for y in ys]; k = len(xs)
    for j in range(1, k):
        for i in range(k - 1, j - 1, -1):
            c[i] = (c[i] - c[i - 1]) / (xs[i] - xs[i - j])
    p = fmpq_poly([c[-1]])
    for i in range(k - 2, -1, -1):
        p = p * fmpq_poly([-xs[i], 1]) + c[i]
    return p

def matmul(A, B):
    return [[sum((A[i][k] * B[k][j] for k in range(len(B))), fmpz_poly(0)) for j in range(len(B[0]))]
            for i in range(len(A))]

def polydet(M):
    D = sum(max(p.degree() for p in row) for row in M) + 1
    xs = list(range(-(D // 2), D - D // 2 + 1))
    ys = [evalmat(M, x).det() for x in xs]
    return interp(xs, ys)

def rank_at(P, x):
    return evalmat(P, x).rank()

def rank_mod(P, f):
    """Exact rank of P over the field Q[t]/(f), f irreducible."""
    f = fmpq_poly(f.coeffs())
    A = [[fmpq_poly(p.coeffs()) % f for p in row] for row in P]
    rows, cols, r = len(A), len(A[0]), 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if not A[i][c].is_zero()), None)
        if piv is None: continue
        A[r], A[piv] = A[piv], A[r]
        g, s, _ = A[r][c].xgcd(f)                   # s*A = g (unit) mod f
        iv = (s / g.coeffs()[0]) % f
        A[r] = [(a * iv) % f for a in A[r]]
        for i in range(rows):
            if i != r and not A[i][c].is_zero():
                h = A[i][c]
                A[i] = [(a - h * b) % f for a, b in zip(A[i], A[r])]
        r += 1
        if r == rows: break
    return r

def torsion(P, n, trials=2, rng=random.Random(1)):
    rk = max(rank_at(P, x) for x in (2, 3, 7))
    G = None
    stable = 0
    while stable < trials:
        L = [[fmpz_poly(rng.randint(-3, 3)) for _ in range(n)] for _ in range(rk)]
        Rm = [[fmpz_poly(rng.randint(-3, 3)) for _ in range(rk)] for _ in range(4 * n)]
        d = polydet(matmul(matmul(L, P), Rm))
        if d.is_zero(): continue                    # singular random combination: retry
        H = d if G is None else G.gcd(d)
        stable = stable + 1 if (G is not None and H.degree() == G.degree()) else 0
        G = H
    num = fmpz_poly((G * G.denom()).numer().coeffs()) if not G.is_zero() else fmpz_poly(0)
    return rk, num

def bimonic(f):
    c = f.coeffs()
    return abs(int(c[0])) == 1 and abs(int(c[-1])) == 1

def analyse(im, n):
    P = polymat(fox(im, n), n)
    rk, T = torsion(P, n)
    if T.is_zero(): return rk, T, [], []
    _, fs = T.factor()
    fs = [(f, e) for f, e in fs if f != fmpz_poly([0, 1])]
    bad = [f for f, e in fs if not bimonic(f)]
    certified = [f for f in bad if rank_mod(P, f) < rk]      # exact: f divides every rk-minor
    return rk, T, fs, certified

def fmt(im):
    return ' '.join('%s=%s' % (g, ''.join(map(str, im[g]))) for g in GENS)

if __name__ == '__main__':
    n = int(sys.argv[1]); maxreps = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
    seen = {}
    for k, im in enumerate(reps(n)):
        if k >= maxreps: break
        rk, T, fs, cert = analyse(im, n)
        key = str(T)
        if key in seen: seen[key][0] += 1; continue
        seen[key] = [1, im]
        print('n=%d rank=%d rep %s' % (n, rk, fmt(im)))
        print('   factors:', ', '.join('(%s)^%d' % (f, e) for f, e in fs))
        print('   non-bimonic certified:', [str(f) for f in cert], flush=True)
    print('n=%d: %d reps, %d distinct torsion orders' % (n, sum(v[0] for v in seen.values()), len(seen)))
