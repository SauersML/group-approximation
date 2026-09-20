"""Exhaustive search of homomorphisms G0 -> PSL(2,p), p odd prime, testing subsets of r5..r8.

G0 = <a,b,c | a^2, b^3, (ab)^4, c^2, (ac)^3>.  In PSL(2,p) every involution is
conjugate to a = [[0,1],[-1,0]], and a must map nontrivially (a -> 1 forces the
trivial map).  So up to conjugacy: a is fixed; b runs over SL(2,p) matrices of
trace +-1 (order 3 in PSL) or b = I, with (ab)^4 = +-I, reduced modulo
conjugation by the centralizer of a; c runs over all trace-0 matrices (the
involutions of PSL) with (ac)^3 = +-I.  A word is trivial in PSL iff its matrix
is +-I.  Matrices are rows (x, y, z, w) = [[x, y], [z, w]].
"""
import sys, itertools
import numpy as np
sys.path.insert(0, 'experiments/thompson-v-models')
sys.path.insert(0, 'experiments/thompson-v-relator-blind-2026-09-17')
from census import load, word_str  # noqa: E402


def mm(X, Y, p):
    return np.stack([(X[..., 0] * Y[..., 0] + X[..., 1] * Y[..., 2]) % p,
                     (X[..., 0] * Y[..., 1] + X[..., 1] * Y[..., 3]) % p,
                     (X[..., 2] * Y[..., 0] + X[..., 3] * Y[..., 2]) % p,
                     (X[..., 2] * Y[..., 1] + X[..., 3] * Y[..., 3]) % p], axis=-1)


def is_pmI(X, p):
    return ((X[..., 1] == 0) & (X[..., 2] == 0) & (X[..., 0] == X[..., 3])
            & ((X[..., 0] == 1) | (X[..., 0] == p - 1)))


def power(X, k, p):
    Rr = np.broadcast_to(np.array([1, 0, 0, 1]), X.shape).copy()
    for _ in range(k):
        Rr = mm(Rr, X, p)
    return Rr


def inv(M, p):
    return np.stack([M[..., 3], (-M[..., 1]) % p, (-M[..., 2]) % p, M[..., 0]], -1)


def trace_class(p, t):
    """All SL(2,p) matrices of trace t."""
    rows = []
    for x in range(p):
        d = (x * (t - x) - 1) % p          # need y*z = d
        w = (t - x) % p
        for y in range(1, p):
            rows.append((x, y, (d * pow(y, p - 2, p)) % p, w))
        if d == 0:
            for z in range(p):
                rows.append((x, 0, z, w))
    return np.array(rows, dtype=np.int64)


def search(p, Rw):
    a = np.array([0, 1, p - 1, 0])
    T1 = np.concatenate([trace_class(p, 1), trace_class(p, p - 1), np.array([[1, 0, 0, 1]])])
    A1 = np.broadcast_to(a, T1.shape)
    Bs = T1[is_pmI(power(mm(A1, T1, p), 4, p), p)]
    T0 = trace_class(p, 0)
    Cs = T0[is_pmI(power(mm(np.broadcast_to(a, T0.shape), T0, p), 3, p), p)]
    cent = np.array([(al, be, (-be) % p, al) for al in range(p) for be in range(p)
                     if (al * al + be * be) % p == 1])
    centi = inv(cent, p)
    seen, reps = set(), []
    for bm in Bs:
        if tuple(bm) in seen:
            continue
        reps.append(bm)
        orb = mm(mm(centi, np.broadcast_to(bm, cent.shape), p), cent, p)
        for o in orb:
            seen.add(tuple(o)); seen.add(tuple((-o) % p))
    solved = {}
    N = len(Cs)
    for bm in reps:
        gens = {'a': np.broadcast_to(a, (N, 4)), 'b': np.broadcast_to(bm, (N, 4)),
                'B': np.broadcast_to(inv(bm, p), (N, 4)), 'c': Cs}
        ok = []
        for w in Rw:
            X = np.broadcast_to(np.array([1, 0, 0, 1]), (N, 4)).copy()
            for ch in w:
                X = mm(X, gens[ch], p)
            ok.append(is_pmI(X, p))
        ok = np.stack(ok)
        for r in range(1, len(Rw) + 1):
            for Sb in itertools.combinations(range(len(Rw)), r):
                if Sb not in solved:
                    hit = np.nonzero(ok[list(Sb)].all(0))[0]
                    if len(hit):
                        solved[Sb] = (tuple(int(v) for v in bm), tuple(int(v) for v in Cs[hit[0]]))
    return len(reps), N, solved


if __name__ == '__main__':
    pmax = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    relfile = sys.argv[2] if len(sys.argv) > 2 else 'experiments/thompson-v-models/rel_V.txt'
    Rw = [word_str(w) for w in load(relfile)]
    names = ['r%d' % (i + 5) for i in range(len(Rw))]
    for p in [q for q in range(3, pmax + 1) if all(q % d for d in range(2, q))]:
        nb, nc, solved = search(p, Rw)
        lab = ['{' + ','.join(names[i] for i in Sb) + '}' for Sb in sorted(solved, key=lambda s: (len(s), s))]
        wit = {'{' + ','.join(names[i] for i in Sb) + '}': v for Sb, v in solved.items() if len(Sb) >= 3}
        print(f'p={p}: b-classes={nb} c-choices={nc} satisfied: {lab} witnesses(>=3): {wit}', flush=True)
