"""Check the vertex-cone compressor lemma on random elements of SL_r(F_p[x^(+-1)]).

For random h (a product of elementary matrices with Laurent monomial entries), take the
column u = h e_1 and the rank-one Y = u v^T with v^T = e_2^T h^(-1). For every exponent m of
Y outside N^d and every i0 with m_i0 < 0, build P in SL_d(Z) with positive entries whose
rows all have one common unique minimizer m* on supp(u) and are negative on m. Check:
  (a) x^(-P m*) (P.u) is a polynomial vector that is unimodular over F_p[x] (Groebner = [1]);
  (b) P m has a negative coordinate (so P.Y is not polynomial: the transfer contradiction).
Also counts how often u itself (P = I, after monomial scaling) is already unimodular.
Run: nice -n 10 timeout 1200 python3 vertex_compressor_check.py [trials] [seed]
"""
import random, sys, itertools, signal
import sympy as sp

p, d, r = 3, 3, 3
X = sp.symbols('x1:%d' % (d + 1))

def madd(a, b):
    c = dict(a)
    for k, v in b.items():
        c[k] = (c.get(k, 0) + v) % p
        if c[k] == 0: del c[k]
    return c

def mmul(a, b):
    c = {}
    for k1, v1 in a.items():
        for k2, v2 in b.items():
            k = tuple(i + j for i, j in zip(k1, k2))
            c[k] = (c.get(k, 0) + v1 * v2) % p
            if c[k] == 0: del c[k]
    return c

def matmul(A, B):
    return [[ (lambda i, j: __import__('functools').reduce(madd, [mmul(A[i][k], B[k][j]) for k in range(r)], {}))(i, j)
              for j in range(r)] for i in range(r)]

def ident():
    return [[{(0,) * d: 1} if i == j else {} for j in range(r)] for i in range(r)]

def elem(i, j, c):
    E = ident(); E[i][j] = c; return E

def neg(c): return {k: (-v) % p for k, v in c.items()}

def random_h(rng, length):
    h, hinv = ident(), ident()
    for _ in range(length):
        i, j = rng.sample(range(r), 2)
        c = {tuple(rng.randint(-2, 2) for _ in range(d)): rng.randint(1, p - 1)}
        h = matmul(h, elem(i, j, c)); hinv = matmul(elem(i, j, neg(c)), hinv)
    return h, hinv

def dot(a, b): return sum(x * y for x, y in zip(a, b))

def unique_min(row, S):
    vals = sorted((dot(row, m), m) for m in S)
    return vals[0][1] if len(vals) == 1 or vals[0][0] < vals[1][0] else None

def build_P(S, m, i0, rng):
    for att in range(400):
        w0 = [1 + rng.randint(0, 3) for _ in range(d)]
        w0[i0] = rng.randint(1, 3); K = rng.randint(2, 12 + att)
        w0 = [x + (K if t == i0 else 0) for t, x in enumerate(w0)]
        ks = [t for t in range(d) if w0[t] == 1]
        if not ks or dot(w0, m) >= 0: continue
        ms = unique_min(w0, S)
        if ms is None: continue
        k = ks[0]
        for N in range(1, 400):
            rows = [w0] + [[(1 if t == j else 0) + N * w0[t] for t in range(d)] for j in range(d) if j != k]
            M = sp.Matrix(rows)
            if M.det() == -1:
                j1 = [j for j in range(d) if j != k][0]  # replace e_j1 + N w0 by -e_j1 + N w0
                rows[1] = [-(1 if t == j1 else 0) + N * w0[t] for t in range(d)]
                M = sp.Matrix(rows)
            if M.det() != 1 or min(min(rw) for rw in rows) <= 0: continue
            if all(unique_min(rw, S) == ms for rw in rows) and all(dot(rw, m) < 0 for rw in rows):
                return rows, ms
    return None, None

def to_poly(c, shift=None, P=None):
    e = 0
    for k, v in c.items():
        kk = k if P is None else tuple(dot(P[i], k) for i in range(d))  # (P k)_i = row_i . k
        if shift is not None: kk = tuple(a - b for a, b in zip(kk, shift))
        assert min(kk) >= 0, kk
        e += v * sp.prod([X[t] ** kk[t] for t in range(d)])
    return e

class Slow(Exception): pass

def _alarm(*a): raise Slow()

def unimodular(polys, limit=30):
    """True/False from a Groebner basis over F_p; None if it takes over `limit` seconds."""
    signal.signal(signal.SIGALRM, _alarm); signal.alarm(limit)
    try:
        G = sp.groebner([q for q in polys if q != 0], *X, modulus=p, order='grevlex')
        return list(G.exprs) == [1]
    except Slow:
        return None
    finally:
        signal.alarm(0)

def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    ok = tested = trivial = skipped = 0
    for t in range(trials):
        h, hinv = random_h(rng, rng.randint(3, 6))
        u = [h[i][0] for i in range(r)]; v = [hinv[1][j] for j in range(r)]
        if t == 0:  # the Koszul-type column of the previous lane: u = (x1,x2,x3), v = (x1^-1,-x2^-1,0)
            u = [{(1, 0, 0): 1}, {(0, 1, 0): 1}, {(0, 0, 1): 1}]
            v = [{(-1, 0, 0): 1}, {(0, -1, 0): p - 1}, {}]
        S = sorted(set(k for c in u for k in c))
        Y = [[mmul(u[i], v[j]) for j in range(r)] for i in range(r)]
        bad = sorted(set(k for row in Y for c in row for k in c if min(k) < 0))
        mu0 = tuple(min(k[t] for k in S) for t in range(d))
        if unimodular([to_poly(c, shift=mu0) for c in u], limit=10): trivial += 1
        for m in bad[:2]:
            i0 = min(t for t in range(d) if m[t] < 0)
            P, ms = build_P(S, m, i0, rng)
            assert P is not None, ("no P found", S, m)
            Pms = tuple(dot(P[i], ms) for i in range(d))
            wp = [to_poly(c, shift=Pms, P=P) for c in u]
            U = unimodular(wp)
            Pm = [dot(P[i], m) for i in range(d)]
            if U is None:
                skipped += 1
            else:
                tested += 1; ok += bool(U) and max(Pm) < 0
            print(f"trial {t}: |supp u|={len(S)} bad m={m} P={P} m*={ms} unimodular={U} Pm={Pm}", flush=True)
    print(f"SUMMARY: {ok}/{tested} (column, bad exponent) pairs certified; "
          f"{trivial}/{trials} columns already unimodular without compressor; "
          f"{skipped} Groebner computations skipped after 30s")

if __name__ == '__main__':
    main()
