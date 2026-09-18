#!/usr/bin/env python3
"""Library and exploratory coatom-mode search for bowties in the noncrossing partition poset [1,c]_W, c = s_1 ... s_n,
for Coxeter groups with labels in {2,3,5} and nondegenerate Tits form (spherical or compact hyperbolic).

Usage: lattice_bowties.py <group> <height bound H> [max certificates to print] [orbit cap]

Library part (used by rank3_bowties.py): exact arithmetic in Z[phi] and Q(sqrt5), the geometric representation,
bounded Hurwitz orbit of the factorization s_1 ... s_n (real roots of height <= H), exact root and reflection tests,
and the wall-form formula of lemma M2 (research/noncrossing-interval-of-5-3-3-11-is-not-a-lattice-proof.md):
  (M1) for z in [1,c]_W, l_T(z) = dim Mov(z), and z <= u <= c in [1,c]_W implies z <= u in O(V);
  (M2) if g <= c in O(V) and Mov(g) = U has basis matrix E, then M = E^T B (1-c)^{-1} E is invertible and
       g = 1 - E M^{-1} E^T B.
Coatom mode (this file's main): for atoms a != b below two coatoms u != v it tries to exclude every element strictly
between, via Mov = span(alpha_a, alpha_b) (and, for n = 5, Mov(u) cap Mov(v)), using M2 and exact reflection tests.
This mode is exploratory; the certificates used in the claim come from rank3_bowties.py and are re-checked by
the independent verifier verify_bowtie.py (determinant criterion, lemma D).  Only lower bounds on the poset are
used, so a certificate does not depend on H.
"""
import sys, itertools, time
from fractions import Fraction as F

# ---------------- Z[phi], phi^2 = phi + 1, as pairs of ints ----------------
def zmul(x, y):
    a, b = x; c, d = y
    return (a*c + b*d, a*d + b*c + b*d)
def zadd(x, y): return (x[0]+y[0], x[1]+y[1])
def zsub(x, y): return (x[0]-y[0], x[1]-y[1])
ZERO, ONE = (0, 0), (1, 0)
PHI = (1 + 5 ** 0.5) / 2
def zfloat(x): return x[0] + x[1]*PHI
def zsign(x):
    p, q = 2*x[0] + x[1], x[1]          # 2(a + b phi) = p + q sqrt5
    if q == 0: return (p > 0) - (p < 0)
    if p == 0: return (q > 0) - (q < 0)
    if (p > 0) == (q > 0): return 1 if p > 0 else -1
    if p*p > 5*q*q: return 1 if p > 0 else -1
    return 1 if q > 0 else -1

# ---------------- Q(sqrt5) as pairs of Fractions (p, q) = p + q sqrt5 ----------------
def qadd(x, y): return (x[0]+y[0], x[1]+y[1])
def qsub(x, y): return (x[0]-y[0], x[1]-y[1])
def qmul(x, y): return (x[0]*y[0] + 5*x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def qinv(x):
    d = x[0]*x[0] - 5*x[1]*x[1]
    return (x[0]/d, -x[1]/d)
def qzero(x): return x[0] == 0 and x[1] == 0
QZ, QO = (F(0), F(0)), (F(1), F(0))
def z2q(z): return (F(z[0]) + F(z[1], 2), F(z[1], 2))
def q_in_zphi(x):                      # p + q sqrt5 = (p - q) + 2q phi
    return (2*x[1]).denominator == 1 and (x[0] - x[1]).denominator == 1
def qm_mul(A, B):
    return [[_qsum(qmul(A[i][l], B[l][j]) for l in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def _qsum(it):
    p = F(0); q = F(0)
    for a, b in it: p += a; q += b
    return (p, q)
def qm_T(A): return [list(r) for r in zip(*A)]
def qm_eye(n): return [[QO if i == j else QZ for j in range(n)] for i in range(n)]
def qm_sub(A, B): return [[qsub(A[i][j], B[i][j]) for j in range(len(A[0]))] for i in range(len(A))]
def qm_inv(A):
    n = len(A); M = [list(A[i]) + qm_eye(n)[i] for i in range(n)]
    for col in range(n):
        piv = next((r for r in range(col, n) if not qzero(M[r][col])), None)
        if piv is None: return None
        M[col], M[piv] = M[piv], M[col]
        ip = qinv(M[col][col]); M[col] = [qmul(ip, x) for x in M[col]]
        for r in range(n):
            if r != col and not qzero(M[r][col]):
                f = M[r][col]; M[r] = [qsub(M[r][j], qmul(f, M[col][j])) for j in range(2*n)]
    return [row[n:] for row in M]
def qm_nullspace(A):
    """basis of {x : A x = 0} (A is k x n) as list of column vectors."""
    k, n = len(A), len(A[0]); M = [list(r) for r in A]; pivots = []; r = 0
    for col in range(n):
        piv = next((i for i in range(r, k) if not qzero(M[i][col])), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        ip = qinv(M[r][col]); M[r] = [qmul(ip, x) for x in M[r]]
        for i in range(k):
            if i != r and not qzero(M[i][col]):
                f = M[i][col]; M[i] = [qsub(M[i][j], qmul(f, M[r][j])) for j in range(n)]
        pivots.append(col); r += 1
        if r == k: break
    free = [j for j in range(n) if j not in pivots]
    basis = []
    for fj in free:
        x = [QZ]*n; x[fj] = QO
        for i, pc in enumerate(pivots):
            x[pc] = qsub(QZ, M[i][fj])
        basis.append(x)
    return basis


def qm_rank(A):
    M = [list(r) for r in A]; rk = 0; rows = len(M); cols = len(M[0])
    for col in range(cols):
        piv = next((r for r in range(rk, rows) if not qzero(M[r][col])), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]
        ip = qinv(M[rk][col]); M[rk] = [qmul(ip, x) for x in M[rk]]
        for r in range(rows):
            if r != rk and not qzero(M[r][col]):
                f = M[r][col]; M[r] = [qsub(M[r][j], qmul(f, M[rk][j])) for j in range(cols)]
        rk += 1
    return rk
def q2z(x):
    assert q_in_zphi(x)
    return (int(x[0] - x[1]), int(2*x[1]))

def root_test(ctx, beta, maxsteps=10000):
    """beta: tuple of Z[phi] pairs with B(beta, beta) = 1.  Returns 'root', 'nonroot' (certified), or 'unknown'.
    Descent: a positive root beta != alpha_i has some i with B(beta, alpha_i) > 0, and s_i beta is again a
    positive root of strictly smaller height (or beta = alpha_i).  A vector with coordinates of both signs is not
    a root."""
    n = ctx.n; T = ctx.T
    signs = {zsign(x) for x in beta} - {0}
    if len(signs) > 1: return 'nonroot'
    if signs == {-1}: beta = tuple((-a, -b) for a, b in beta)
    for _ in range(maxsteps):
        nz = [i for i in range(n) if beta[i] != ZERO]
        if len(nz) == 1 and beta[nz[0]] == ONE: return 'root'
        moved = False
        for i in range(n):
            e = tuple(ONE if j == i else ZERO for j in range(n))
            k = pair2B(T, beta, e)        # 2 B(beta, alpha_i)
            if zsign(k) > 0:
                beta = reflect(T, e, beta)
                s = {zsign(x) for x in beta} - {0}
                if s != {1}: return 'nonroot'
                moved = True; break
        if not moved: return 'nonroot'      # positive vector with B(beta,beta)=1 and all B(beta,alpha_i) <= 0
    return 'unknown'

def reflection_test(ctx, g):
    """g: Q(sqrt5) matrix. 'refl' if g is a reflection of W, 'no' if certified not, 'unknown'."""
    n = ctx.n
    if not all(q_in_zphi(x) for row in g for x in row): return 'no'
    D = qm_sub(qm_eye(n), g)
    if qm_rank(D) != 1: return 'no'
    col = next(j for j in range(n) if any(not qzero(D[i][j]) for i in range(n)))
    v = [D[i][col] for i in range(n)]
    # (1 - s_beta) x = 2B(x, beta) beta ; beta proportional to v, with B(beta,beta)=1
    Bv = qm_mul(qm_mul([v], ctx.Bq), [[x] for x in v])[0][0]
    if qzero(Bv): return 'no'
    # beta = v / sqrt(B(v,v)); need B(v,v) = t^2 with t in Q(sqrt5)
    p, q = Bv
    t = None
    import fractions
    # solve (x + y sqrt5)^2 = p + q sqrt5 : x^2 + 5 y^2 = p, 2xy = q
    from math import isqrt
    def fsqrt(fr):
        if fr < 0: return None
        a, b = fr.numerator, fr.denominator
        ra, rb = isqrt(a), isqrt(b)
        return F(ra, rb) if ra*ra == a and rb*rb == b else None
    if q == 0:
        s_ = fsqrt(p)
        if s_ is not None: t = (s_, F(0))
        else:
            s_ = fsqrt(p / 5)
            if s_ is not None: t = (F(0), s_)
    else:
        # x^2 = (p +- sqrt(p^2 - 5 q^2)) / 2
        d = fsqrt(p*p - 5*q*q)
        if d is not None:
            for x2 in ((p + d) / 2, (p - d) / 2):
                x = fsqrt(x2)
                if x and x != 0:
                    t = (x, q / (2*x)); break
    if t is None: return 'no'
    ti = qinv(t)
    beta = [qmul(ti, x) for x in v]
    if not all(q_in_zphi(x) for x in beta): return 'no'
    bz = tuple(q2z(x) for x in beta)
    # check g really is s_beta
    sb = [[z2q(x) for x in row] for row in refl_matrix(ctx.T, bz)]
    if sb != g: return 'no'
    r = root_test(ctx, bz)
    return {'root': 'refl', 'nonroot': 'no', 'unknown': 'unknown'}[r]

# ---------------- groups ----------------
def twoB_entry(m):
    return {1: (2, 0), 2: (0, 0), 3: (-1, 0), 5: (0, -1)}[m]
GROUPS = {
    # finite calibration
    'A3':    (3, {(0,1):3, (1,2):3}),
    'H3':    (3, {(0,1):5, (1,2):3}),
    'A4':    (4, {(0,1):3, (1,2):3, (2,3):3}),
    'D4':    (4, {(0,2):3, (1,2):3, (2,3):3}),
    'H4':    (4, {(0,1):5, (1,2):3, (2,3):3}),
    'A5':    (5, {(0,1):3, (1,2):3, (2,3):3, (3,4):3}),
    'D5':    (5, {(0,1):3, (1,2):3, (2,3):3, (2,4):3}),
    # rank 3 hyperbolic (lattice by Delucchi-Paolini-Salvetti; no rank-(1,2) bowtie is possible)
    '335':   (3, {(0,1):3, (1,2):5, (0,2):3}),
    # rank 4 compact hyperbolic (Lanner) with labels in {2,3,5}
    '353':   (4, {(0,1):3, (1,2):5, (2,3):3}),
    '535':   (4, {(0,1):5, (1,2):3, (2,3):5}),
    '5311':  (4, {(0,1):5, (1,2):3, (1,3):3}),
    # rank 5 compact hyperbolic (Lanner) with labels in {2,3,5}
    '5333':  (5, {(0,1):5, (1,2):3, (2,3):3, (3,4):3}),
    '5335':  (5, {(0,1):5, (1,2):3, (2,3):3, (3,4):5}),
    '53311': (5, {(0,1):5, (1,2):3, (2,3):3, (2,4):3}),
}

def setup(name):
    n, edges = GROUPS[name]
    T = [[twoB_entry(1) if i == j else ZERO for j in range(n)] for i in range(n)]
    for (i, j), m in edges.items():
        T[i][j] = T[j][i] = twoB_entry(m)
    return n, T

def pair2B(T, x, y):
    acc = ZERO; n = len(x)
    for i in range(n):
        if x[i] == ZERO: continue
        for j in range(n):
            if y[j] == ZERO or T[i][j] == ZERO: continue
            acc = zadd(acc, zmul(zmul(x[i], T[i][j]), y[j]))
    return acc
def reflect(T, beta, x):             # s_beta(x) = x - 2B(x, beta) beta   (B(beta, beta) = 1 for real roots)
    k = pair2B(T, x, beta)
    return tuple(zsub(x[i], zmul(k, beta[i])) for i in range(len(x)))
def normalize(r):
    for x in r:
        s = zsign(x)
        if s: return r if s > 0 else tuple((-a, -b) for a, b in r)
    raise ValueError('zero root')
def height(r): return sum(abs(zfloat(x)) for x in r)
def refl_matrix(T, beta):
    n = len(beta)
    cols = [reflect(T, beta, tuple(ONE if i == j else ZERO for i in range(n))) for j in range(n)]
    return tuple(tuple(cols[j][i] for j in range(n)) for i in range(n))
def zm_mul(X, Y):
    n = len(X)
    out = []
    for i in range(n):
        row = []
        for j in range(n):
            a = b = 0
            for k in range(n):
                p = X[i][k]; q = Y[k][j]
                if p == ZERO or q == ZERO: continue
                u, v = zmul(p, q); a += u; b += v
            row.append((a, b))
        out.append(tuple(row))
    return tuple(out)

def hurwitz_orbit(n, T, H, cap):
    start = tuple(tuple(ONE if i == j else ZERO for i in range(n)) for j in range(n))
    seen = {start}; frontier = [start]; closed = True
    while frontier:
        nxt = []
        for f in frontier:
            for i in range(n - 1):
                a, b = f[i], f[i+1]
                for new in ((normalize(reflect(T, a, b)), a), (b, normalize(reflect(T, b, a)))):
                    if height(new[0]) > H or height(new[1]) > H: continue
                    g = f[:i] + new + f[i+2:]
                    if g not in seen:
                        seen.add(g); nxt.append(g)
                        if len(seen) >= cap: return seen, False
        frontier = nxt
    return seen, closed

class Ctx:
    def __init__(self, n, T):
        self.n, self.T = n, T
        self.Bq = [[(F(T[i][j][0]) + F(T[i][j][1], 2), F(T[i][j][1], 2)) for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(n):
                self.Bq[i][j] = (self.Bq[i][j][0] / 2, self.Bq[i][j][1] / 2)
        self.rm = {}
        c = None
        for j in range(n):
            e = tuple(ONE if i == j else ZERO for i in range(n))
            c = self.R(e) if c is None else zm_mul(c, self.R(e))
        self.c = c
        cq = [[z2q(x) for x in row] for row in c]
        inv = qm_inv(qm_sub(qm_eye(n), cq))
        assert inv is not None, '1 - c singular (degenerate form?)'
        self.chi = qm_mul(self.Bq, inv)      # chi_c(u, v) = u^T B (1-c)^{-1} v
    def R(self, beta):
        if beta not in self.rm: self.rm[beta] = refl_matrix(self.T, beta)
        return self.rm[beta]
    def prod(self, roots):
        m = None
        for r in roots:
            m = self.R(r) if m is None else zm_mul(m, self.R(r))
        return m
    def z_of_subspace(self, E):
        """E: list of column vectors (Q(sqrt5)). Returns None if chi_c|U degenerate, else the matrix z_U."""
        Em = qm_T(E)                          # n x k
        M = qm_mul(qm_mul(qm_T(Em), self.chi), Em)
        Mi = qm_inv(M)
        if Mi is None: return None
        return qm_sub(qm_eye(self.n), qm_mul(qm_mul(qm_mul(Em, Mi), qm_T(Em)), self.Bq))

def verdict(ctx, E):
    z = ctx.z_of_subspace(E)
    if z is None: return 'degenerate', None
    if all(q_in_zphi(x) for row in z for x in row): return 'integral', z
    return 'nonintegral', z

def main():
    name = sys.argv[1]; H = float(sys.argv[2]); show = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 300000
    n, T = setup(name); ctx = Ctx(n, T); t0 = time.time()
    facts, closed = hurwitz_orbit(n, T, H, cap)
    print(f'[{name}] n={n} H={H}: {len(facts)} reduced reflection factorizations of c (orbit closed under bounded moves: {closed})')
    # sanity: every factorization multiplies to c
    bad = sum(1 for f in list(facts)[:2000] if ctx.prod(f) != ctx.c)
    assert bad == 0, 'factorization does not multiply to c'
    # atoms below coatoms; coatom keyed by its matrix
    coatom_atoms = {}; coatom_fact = {}; witness = {}
    for f in facts:
        for d in range(n):
            rest = f[:d] + f[d+1:]
            u = ctx.prod(rest)
            coatom_atoms.setdefault(u, set()).update(rest)
            coatom_fact.setdefault(u, rest)
            for r in rest: witness.setdefault((u, r), rest)
    print(f'  coatoms in P_H: {len(coatom_atoms)}; atoms: {len({r for f in facts for r in f})} [{time.time()-t0:.1f}s]')
    # check formula (M2) on the elements we can build exactly: rank 2 and rank n-2 subsequence products
    checked = 0
    for f in list(facts)[:300]:
        for k in sorted({2, n - 2}):
            for S in itertools.combinations(range(n), k):
                roots = [f[i] for i in S]
                z = ctx.z_of_subspace([[z2q(x) for x in r] for r in roots])
                zz = [[z2q(x) for x in row] for row in ctx.prod(roots)]
                assert z is not None and z == zz, 'Mov/chi formula disagrees with an actual element'
                checked += 1
    print(f'  formula (M2) verified on {checked} actual elements')
    pair_coatoms = {}
    for u, ats in coatom_atoms.items():
        for a, b in itertools.combinations(sorted(ats), 2):
            pair_coatoms.setdefault((a, b), []).append(u)
    multi = {p: us for p, us in pair_coatoms.items() if len(us) >= 2}
    print(f'  atom pairs below >= 2 coatoms: {len(multi)} [{time.time()-t0:.1f}s]')
    stats = {}; certs = []
    qcache = {}
    def Q(m):
        if m not in qcache: qcache[m] = [[z2q(x) for x in row] for row in m]
        return qcache[m]
    def excluded_z2(a, b, z):
        """True if certified: no z' in [1,c]_W with Mov(z') = U2 lies above a and b (rank-2 case)."""
        if z is None or not all(q_in_zphi(x) for row in z for x in row): return True, 'deg/nonint'
        ra = reflection_test(ctx, qm_mul(Q(ctx.R(a)), z)); rb = reflection_test(ctx, qm_mul(Q(ctx.R(b)), z))
        if 'no' in (ra, rb): return True, 'a.z or b.z not a reflection'
        return False, (ra, rb)
    for (a, b), us in multi.items():
        v2, z2 = verdict(ctx, [[z2q(x) for x in a], [z2q(x) for x in b]])
        ex2, why2 = excluded_z2(a, b, z2)
        if n == 4:
            if ex2:
                key = ('certified', why2); certs.append((a, b, us[0], us[1], why2, None))
            else:
                zi = qm_inv(z2)
                res = {u: reflection_test(ctx, qm_mul(zi, Q(u))) for u in us}
                nos = [u for u in us if res[u] == 'no']
                if nos:
                    other = next(u for u in us if u != nos[0])
                    key = ('certified', 'z^-1 u not a reflection'); certs.append((a, b, nos[0], other, 'z^-1 u not a reflection', None))
                elif all(r == 'refl' for r in res.values()):
                    key = ('join exists below all coatoms',)
                else:
                    key = ('unknown',)
            stats[key] = stats.get(key, 0) + 1
        elif n == 5:
            fixes = {}
            for u in us:
                ns = qm_nullspace(qm_sub(qm_eye(n), Q(u))); assert len(ns) == 1
                fixes[u] = ns[0]
            rank2_ok = {}
            if not ex2:
                zi2 = qm_inv(z2)
                for u in us:
                    rank2_ok[u] = qm_rank(qm_sub(qm_eye(n), qm_mul(zi2, Q(u)))) == 2
            for u, v in itertools.combinations(us, 2):
                e2 = ex2 or not rank2_ok[u] or not rank2_ok[v]
                rows = [qm_mul([fixes[w]], ctx.Bq)[0] for w in (u, v)]
                U3 = qm_nullspace(rows); assert len(U3) == 3
                v3, z3 = verdict(ctx, U3)
                if v3 != 'integral': e3, why3 = True, v3
                else:
                    zi3 = qm_inv(z3)
                    e3 = False; why3 = 'open'
                    if any(qm_rank(qm_sub(qm_eye(n), qm_mul(Q(ctx.R(x)), z3))) != 2 for x in (a, b)):
                        e3, why3 = True, 'dim Mov(a z3) != 2'
                    else:
                        ru = reflection_test(ctx, qm_mul(zi3, Q(u))); rv = reflection_test(ctx, qm_mul(zi3, Q(v)))
                        if 'no' in (ru, rv): e3, why3 = True, 'z3^-1 u not a reflection'
                key = ('U2 excluded' if e2 else 'U2 open', 'U3 excluded' if e3 else 'U3 open')
                stats[key] = stats.get(key, 0) + 1
                if e2 and e3:
                    certs.append((a, b, u, v, why2 if ex2 else 'dim Mov(z2^-1 u) != 2', why3))
        else:
            print('  certification implemented for n = 4, 5 only'); return
    print(f'  verdicts (U2[, U3]) over candidate configurations: {stats}')
    print(f'  CERTIFIED BOWTIES: {len(certs)} [{time.time()-t0:.1f}s]')
    for a, b, u, v, v2, v3 in certs[:show]:
        print('    atoms  alpha_a =', a, ' alpha_b =', b, '  (Z[phi] coords (x, y) = x + y*phi)')
        print('    coatom u = product of roots', witness[(u, a)], '=', witness[(u, b)])
        print('    coatom v = product of roots', witness[(v, a)], '=', witness[(v, b)])
        print('    z_U2:', v2, '' if v3 is None else f' z_U3: {v3}')
    import os, json
    if os.environ.get('CERT_OUT') and not certs and os.environ.get('CONTROL'):
        (a, b), us = next(iter(multi.items()))           # negative control: a non-certified candidate
        certs_ctrl = [(a, b, us[0], us[1], 'control', None)]
    else:
        certs_ctrl = certs
    if os.environ.get('CERT_OUT') and certs_ctrl:
        a, b, u, v, v2, v3 = certs_ctrl[0]
        json.dump({'group': name, 'n': n, 'edges': [[i, j, m] for (i, j), m in GROUPS[name][1].items()],
                   'alpha_a': a, 'alpha_b': b, 'u_facts': [witness[(u, a)], witness[(u, b)]], 'v_facts': [witness[(v, a)], witness[(v, b)]],
                   'reason_U2': v2, 'reason_U3': v3}, open(os.environ['CERT_OUT'], 'w'), indent=1)
        print('  first certificate written to', os.environ['CERT_OUT'])
    return len(certs)

if __name__ == '__main__':
    main()
