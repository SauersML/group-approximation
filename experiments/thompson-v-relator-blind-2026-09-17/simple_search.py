"""Exhaustive Hom(G0, S) for small simple groups S not covered by census.py or the PGL(2) proofs.

G0 = <a,b,c | a^2, b^3, (ab)^4, c^2, (ac)^3>.  A homomorphism with a -> 1 is trivial.  Up to
conjugacy a -> one representative of each involution class of S; then b ranges over all
elements with b^3 = 1 and (ab)^4 = 1, and c over all involutions with (ac)^3 = 1.  Every such
triple is a homomorphism, and every homomorphism with a != 1 is conjugate to one of them.  For
each triple we test r5..r8 exactly.

Groups (projective matrix groups, elements normalised mod scalars, full element lists by BFS):
  U3(3) < PGL(3,9), L3(4) < PGL(3,4), U4(2) = PSp(4,3) < PGL(4,3), U3(4) < PGL(3,16),
  U3(5) < PGL(3,25), J1 < GL(7,11) (Janko's generators), L3(5) < PGL(3,5).
The group order is asserted, so a wrong construction fails loudly.
"""
import sys, itertools, random
import numpy as np
sys.path.insert(0, 'experiments/thompson-v-models')
sys.path.insert(0, 'experiments/thompson-v-relator-blind-2026-09-17')
from census import load, word_str  # noqa: E402


class GF:
    MOD = {4: (2, [1, 1, 1]), 9: (3, [1, 0, 1]), 16: (2, [1, 1, 0, 0, 1]), 25: (5, [3, 0, 1])}

    def __init__(self, q):
        self.q = q
        if q in self.MOD:
            p, mod = self.MOD[q]
        else:
            p, mod = q, None
        self.p = p
        k = len(mod) - 1 if mod else 1
        coeff = lambda e: [(e // p ** i) % p for i in range(k)]
        enc = lambda cs: sum(int(c) * p ** i for i, c in enumerate(cs))
        add = np.zeros((q, q), np.int64); mul = np.zeros((q, q), np.int64)
        for x in range(q):
            for y in range(q):
                cx, cy = coeff(x), coeff(y)
                add[x, y] = enc([(u + v) % p for u, v in zip(cx, cy)])
                prod = [0] * (2 * k)
                for i in range(k):
                    for j in range(k):
                        prod[i + j] += cx[i] * cy[j]
                if mod:
                    for d in range(2 * k - 1, k - 1, -1):
                        c = prod[d] % p
                        if c:
                            for i in range(k + 1):
                                prod[d - k + i] -= c * mod[i]
                mul[x, y] = enc([c % p for c in prod[:k]])
        self.add, self.mul = add, mul
        self.neg = np.array([int(np.nonzero(add[x] == 0)[0][0]) for x in range(q)])
        self.inv = np.zeros(q, np.int64)
        for x in range(1, q):
            self.inv[x] = int(np.nonzero(mul[x] == 1)[0][0])
        assert all(len(set(mul[x])) == q for x in range(1, q)), 'not a field'

    def el(self, n):          # integer n in the prime field
        return n % self.p

    def pw(self, x, e):
        r = 1
        for _ in range(e):
            r = self.mul[r, x]
        return r


def _mm(F, A, B):
    P = F.mul[A[..., :, :, None], B[..., None, :, :]]
    C = P[..., :, 0, :]
    for k in range(1, A.shape[-1]):
        C = F.add[C, P[..., :, k, :]]
    return C


def mm(F, A, B, chunk=20000):
    A, B = np.broadcast_arrays(A, B)
    if A.ndim == 2 or len(A) <= chunk:
        return _mm(F, A, B)
    return np.concatenate([_mm(F, A[i:i + chunk], B[i:i + chunk]) for i in range(0, len(A), chunk)])


def normalize(F, A):
    n = A.shape[-1]
    flat = A.reshape(-1, n * n)
    idx = np.argmax(flat != 0, axis=1)
    lead = flat[np.arange(len(flat)), idx]
    return F.mul[flat, F.inv[lead][:, None]].reshape(A.shape)


def bfs(F, gens, expect):
    n = gens[0].shape[0]
    I = np.eye(n, dtype=np.int64)
    seen = {normalize(F, I[None])[0].astype(np.uint8).tobytes()}
    elems = [normalize(F, I[None])[0]]
    front = np.array(elems)
    G = normalize(F, np.array(gens))
    while len(front):
        new = []
        for g in G:
            for chunk in range(0, len(front), 50000):
                X = normalize(F, mm(F, front[chunk:chunk + 50000], g[None]))
                for x in X:
                    key = x.astype(np.uint8).tobytes()
                    if key not in seen:
                        seen.add(key); new.append(x)
        front = np.array(new) if new else np.zeros((0, n, n), np.int64)
        elems += new
        if len(elems) > expect:
            break
    E = np.array(elems)
    assert len(E) == expect, ('order', len(E), expect)
    return E


def outer(F, w, v, al):
    n = len(v)
    M = np.eye(n, dtype=np.int64)
    for i in range(n):
        for j in range(n):
            M[i, j] = F.add[M[i, j], F.mul[al, F.mul[w[i], v[j]]]]
    return M


def unitary(q0, expect, seed=1):
    F = GF(q0 * q0)
    sig = lambda x: F.pw(x, q0)
    n = 3
    herm = lambda x, y: _herm(F, sig, x, y)
    iso = [v for v in itertools.product(range(F.q), repeat=n) if any(v) and herm(v, v) == 0]
    tz = [x for x in range(1, F.q) if F.add[x, sig(x)] == 0]
    rnd = random.Random(seed)
    gens = []
    for _ in range(8):
        v = rnd.choice(iso)
        w = [sig(v[n - 1 - i]) for i in range(n)]
        gens.append(outer(F, w, v, rnd.choice(tz)))
    return F, bfs(F, gens, expect)


def _herm(F, sig, x, y):
    n = len(x)
    s = 0
    for i in range(n):
        s = F.add[s, F.mul[x[i], sig(y[n - 1 - i])]]
    return s


def sp43(expect=25920, seed=2):
    F = GF(3)
    Om = {0: (3, 1), 1: (2, 1), 2: (1, 2), 3: (0, 2)}   # w_i = +-v_j
    rnd = random.Random(seed)
    gens = []
    for v in itertools.product(range(2), repeat=4):   # transvections along all 0/1 vectors
        if not any(v):
            continue
        w = [F.mul[Om[i][1], v[Om[i][0]]] for i in range(4)]
        gens.append(outer(F, w, v, 1))
    return F, bfs(F, gens, expect)


def sl3(q, expect):
    F = GF(q)
    gens = []
    k = len(F.MOD[q][1]) - 1 if q in F.MOD else 1
    basis = [F.p ** i for i in range(k)]          # 1, x, ..., x^(k-1): an F_p-basis
    for i, j in ((0, 1), (1, 2), (2, 0)):
        for al in basis:
            M = np.eye(3, dtype=np.int64); M[i, j] = al; gens.append(M)
    return F, bfs(F, gens, expect)


def j1():
    F = GF(11)
    Y = np.zeros((7, 7), np.int64)
    for i in range(7):
        Y[i, (i + 1) % 7] = 1
    Z = -np.array([[-3, 2, -1, -1, -3, -1, -3], [-2, 1, 1, 3, 1, 3, 3], [-1, -1, -3, -1, -3, -3, 2],
                   [-1, -3, -1, -3, -3, 2, -1], [-3, -1, -3, -3, 2, -1, -1], [1, 3, 3, -2, 1, 1, 3],
                   [3, 3, -2, 1, 1, 3, 1]]) % 11
    return F, bfs(F, [Y, Z], 175560)


def search(name, F, E, Rw, maxord=40):
    n = E.shape[-1]
    N = len(E)
    Ikey = normalize(F, np.eye(n, dtype=np.int64)[None])[0]
    isI = lambda X: (normalize(F, X).reshape(len(X), -1) == Ikey.reshape(-1)).all(1)
    index = {e.astype(np.uint8).tobytes(): i for i, e in enumerate(E)}
    order = np.zeros(N, np.int64); invi = np.zeros(N, np.int64)
    P = E.copy(); prev = np.broadcast_to(Ikey, E.shape).copy()
    for m in range(1, maxord + 1):
        hit = isI(P) & (order == 0)
        for i in np.nonzero(hit)[0]:
            order[i] = m; invi[i] = index[normalize(F, prev[i][None])[0].astype(np.uint8).tobytes()]
        if (order > 0).all():
            break
        prev = P
        P = normalize(F, mm(F, P, E))
    assert (order > 0).all()
    invs = np.nonzero(order == 2)[0]
    o3 = np.nonzero((order == 3) | (order == 1))[0]
    seen, reps = set(), []
    for i in invs:
        if i in seen:
            continue
        reps.append(i)
        cls = normalize(F, mm(F, mm(F, E[invi], np.broadcast_to(E[i], E.shape)), E))
        seen |= {index[x.astype(np.uint8).tobytes()] for x in cls}
    names = ['r5', 'r6', 'r7', 'r8']
    total = 0
    sat = {}
    for ai in reps:
        a = E[ai]
        Bs = E[o3]; Bs = Bs[isI(_pow(F, mm(F, np.broadcast_to(a, Bs.shape), Bs), 4))]
        Binv = np.array([E[invi[index[b.astype(np.uint8).tobytes()]]] for b in Bs])
        Cs = E[invs]; Cs = Cs[isI(_pow(F, mm(F, np.broadcast_to(a, Cs.shape), Cs), 3))]
        total += len(Bs) * len(Cs)
        for bi in range(len(Bs)):
            gens = {'a': np.broadcast_to(a, Cs.shape), 'b': np.broadcast_to(Bs[bi], Cs.shape),
                    'B': np.broadcast_to(Binv[bi], Cs.shape), 'c': Cs}
            oks = []
            for w in Rw:
                X = np.broadcast_to(Ikey, Cs.shape).copy()
                for ch in w:
                    X = normalize(F, mm(F, X, gens[ch]))
                oks.append(isI(X))
            for k in (4, 5, 6, 7, 8):      # controls: the evaluator must see (bc)^k = 1 when it holds
                X = np.broadcast_to(Ikey, Cs.shape).copy()
                for ch in 'bc' * k:
                    X = normalize(F, mm(F, X, gens[ch]))
                sat['ctrl(bc)^%d' % k] = sat.get('ctrl(bc)^%d' % k, 0) + int(isI(X).sum())
            for r in range(1, 5):
                for S in itertools.combinations(range(4), r):
                    cnt = int(np.stack([oks[i] for i in S]).all(0).sum())
                    lab = '{' + ','.join(names[i] for i in S) + '}'
                    sat[lab] = sat.get(lab, 0) + cnt
    print(f'{name}: |S|={N} involution classes={len(reps)} homs(a=rep)={total} '
          f'solutions per subset: {sat}', flush=True)
    return sat


def _pow(F, X, k):
    R = X
    for _ in range(k - 1):
        R = normalize(F, mm(F, R, X))
    return R


if __name__ == '__main__':
    Rw = [word_str(w) for w in load('experiments/thompson-v-models/rel_V.txt')]
    which = sys.argv[1:] or ['U3(3)', 'L3(4)', 'U4(2)', 'U3(4)', 'U3(5)', 'J1', 'L3(5)']
    build = {'U3(3)': lambda: unitary(3, 6048), 'L3(4)': lambda: sl3(4, 20160),
             'U4(2)': lambda: sp43(), 'U3(4)': lambda: unitary(4, 62400),
             'U3(5)': lambda: unitary(5, 126000), 'J1': j1, 'L3(5)': lambda: sl3(5, 372000)}
    for nm in which:
        F, E = build[nm]()
        search(nm, F, E, Rw)
