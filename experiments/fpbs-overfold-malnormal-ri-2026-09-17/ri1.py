"""k = 1 relative-inertia hunt with NON-normal X (swarm-0917-w19-w19-fp-follow).

(RI_B) at k = 1:  X <= B, J = <X, g>  ==>  rk((J cap B) : X) <= 1.

For each trial we build Y = J cap B by Stallings pullback and look for a
certificate that rk(Y : X) >= 2:
  * Z-homology: the cokernel of H_1(X) -> H_1(Y) needs >= 2 generators
    (checked as max over p in {0, primes <= 47} of dim coker (x) F_p);
  * finite quotient: an onto hom rho: Y -> G with <rho(X), h> != G for all h.
Any certificate is a violation of (RI_B) at k = 1 (rk(J : X) <= 1).

usage: python3 ri1.py selftest
       python3 ri1.py MODE SEED TRIALS     MODE = L1 | L2 | malr2 | anyr2
"""
import random
import sys
from fractions import Fraction
from itertools import product
from stall import red, inv, fold_graph, member, rank, basis, coords, intersect, L
from maln import malnormal


# ---------- small permutation groups ----------
def pmul(p, q):  # apply p then q
    return tuple(q[i] for i in p)


def pinv(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def closure(gens, n):
    e = tuple(range(n))
    S = {e}
    frontier = [e]
    while frontier:
        nf = []
        for x in frontier:
            for g in gens:
                y = pmul(x, g)
                if y not in S:
                    S.add(y)
                    nf.append(y)
        frontier = nf
    return frozenset(S)


def cyc(n, *cycles):
    p = list(range(n))
    for c in cycles:
        for i in range(len(c)):
            p[c[i]] = c[(i + 1) % len(c)]
    return tuple(p)


GENS = {
    'C2C2': ([cyc(4, (0, 1)), cyc(4, (2, 3))], 4),
    'S3': ([cyc(3, (0, 1, 2)), cyc(3, (0, 1))], 3),
    'D4': ([cyc(4, (0, 1, 2, 3)), cyc(4, (0, 2))], 4),
    'Q8': ([(1, 4, 3, 6, 5, 0, 7, 2), (2, 7, 4, 1, 6, 3, 0, 5)], 8),
    'A4': ([cyc(4, (0, 1, 2)), cyc(4, (0, 1), (2, 3))], 4),
    'C3C3': ([cyc(6, (0, 1, 2)), cyc(6, (3, 4, 5))], 6),
    'D5': ([cyc(5, (0, 1, 2, 3, 4)), cyc(5, (1, 4), (2, 3))], 5),
    'S4': ([cyc(4, (0, 1, 2, 3)), cyc(4, (0, 1))], 4),
    'A5': ([cyc(5, (0, 1, 2, 3, 4)), cyc(5, (0, 1, 2))], 5),
}
GROUPS = {nm: (sorted(closure(g, n)), n) for nm, (g, n) in GENS.items()}
_relcache = {}


def one_more_generates(nm, A):
    """Is there h in G with <A, h> = G ?"""
    key = (nm, A)
    if key not in _relcache:
        els, n = GROUPS[nm]
        _relcache[key] = any(len(closure(list(A) + [h], n)) == len(els) for h in els)
    return _relcache[key]


def evalw(cw, imgs, n):
    r = tuple(range(n))
    for (i, s) in cw:
        r = pmul(r, imgs[i] if s == 1 else pinv(imgs[i]))
    return r


# ---------- homology ----------
PRIMES = [0, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]


def rank_mod(M, r, p):
    A = [[(Fraction(x) if p == 0 else x % p) for x in row] for row in M]
    rk = 0
    rows = len(A)
    for col in range(r):
        piv = next((i for i in range(rk, rows) if A[i][col] != 0), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        pv = A[rk][col]
        for i in range(rows):
            if i != rk and A[i][col] != 0:
                if p == 0:
                    f = A[i][col] / pv
                    A[i] = [x - f * y for x, y in zip(A[i], A[rk])]
                else:
                    f = A[i][col] * pow(pv, p - 2, p) % p
                    A[i] = [(x - f * y) % p for x, y in zip(A[i], A[rk])]
        rk += 1
    return rk


def dcoker(M, r):
    """Lower bound (exact up to primes > 47) for d(Z^r / rowspace M)."""
    if not M:
        return r
    return max(r - rank_mod(M, r, p) for p in PRIMES)


# ---------- certificate ----------
def certify(YG, Xgens, maxenum=3 * 10 ** 5, nsample=20000):
    """Return a certificate string if rk(Y : X) >= 2 is proved, else None."""
    Bs = basis(YG)
    r = len(Bs[1])
    cx = [coords(YG, Bs, w) for w in Xgens]
    M = []
    for c in cx:
        row = [0] * r
        for (i, s) in c:
            row[i] += s
        M.append(row)
    h = dcoker(M, r)
    if h >= 2:
        return 'homology d(coker)=%d' % h
    for nm, (els, n) in GROUPS.items():
        N = len(els)
        if N ** r > maxenum:
            it = (tuple(random.choice(els) for _ in range(r)) for _ in range(nsample))
        else:
            it = product(els, repeat=r)
        for imgs in it:
            if len(closure(list(imgs), n)) != N:
                continue
            A = closure([evalw(c, imgs, n) for c in cx], n)
            if not one_more_generates(nm, A):
                return 'quotient %s |rho(X)|=%d imgs=%s' % (nm, len(A), imgs)
    return None


# ---------- random words ----------
INVL = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def randword(rng, lmin, lmax):
    n = rng.randint(lmin, lmax)
    w = ''
    while len(w) < n:
        x = rng.choice('aAbB')
        if w and w[-1] == INVL[x]:
            continue
        w += x
    return w


def subst(word, gens):
    m = {'a': gens[0], 'A': inv(gens[0]), 'b': gens[1], 'B': inv(gens[1])}
    return red(''.join(m[x] for x in word))


def main():
    mode, seed, trials = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    random.seed(seed)
    stats = dict(trials=0, nontriv=0, certified=0, big=0, JcontainsB=0)
    fixed = {'L1': L(1), 'L2': L(2)}.get(mode)
    for t in range(trials):
        if fixed:
            Bg = fixed
        else:
            while True:
                Bg = [randword(rng, 2, 6) for _ in range(2)]
                BG = fold_graph(Bg)
                if rank(BG) == 2 and (mode == 'anyr2' or malnormal(BG)):
                    break
        BG = fold_graph(Bg)
        nx = rng.choice([1, 2, 2, 3])
        Xg = [subst(randword(rng, 1, 6), Bg) for _ in range(nx)]
        XG = fold_graph(Xg)
        if rank(XG) == 0:
            continue
        Xb = basis(XG)[1]
        g = randword(rng, 1, 7)
        if not g or member(BG, g):
            continue
        JG = fold_graph(Xb + [g])
        YG = intersect(JG, BG)
        stats['trials'] += 1
        Yb = basis(YG)[1]
        if all(member(XG, w) for w in Yb):
            continue  # Y = X
        stats['nontriv'] += 1
        if all(member(JG, w) for w in Bg):
            stats['JcontainsB'] += 1
        if len(Yb) > 5:
            stats['big'] += 1
            continue
        c = certify(YG, Xb)
        if c:
            stats['certified'] += 1
            print('VIOLATION B=%s mal=%s X=%s g=%s rkY=%d rkJ=%d cert=%s'
                  % (Bg, malnormal(BG), Xb, g, len(Yb), rank(JG), c), flush=True)
    print('STATS', mode, seed, stats)


def main_G(j=1):
    """(G_j) hunt: M = <X0, g> with X0 <= L_{j+1} random, g in F random.
    X = M cap L_{j+1}, Y = M cap L_j, rk(M : X) <= 1.  Violation iff rk(Y : X) >= 2."""
    seed, trials = int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    random.seed(seed)
    Lj, Lj1 = L(j), L(j + 1)
    LjG, Lj1G = fold_graph(Lj), fold_graph(Lj1)
    stats = dict(trials=0, nontriv=0, certified=0, big=0, rkY=[0] * 12)
    for t in range(trials):
        nx = rng.choice([1, 1, 2, 2, 3])
        X0 = [subst(randword(rng, 1, 5), Lj1) for _ in range(nx)]
        X0 = [w for w in X0 if w]
        if not X0:
            continue
        g = randword(rng, 1, 8)
        if not g:
            continue
        MG = fold_graph(X0 + [g])
        XG = intersect(MG, Lj1G)
        YG = intersect(MG, LjG)
        Xb = basis(XG)[1]
        Yb = basis(YG)[1]
        stats['trials'] += 1
        if all(member(XG, w) for w in Yb):
            continue
        stats['nontriv'] += 1
        stats['rkY'][min(len(Yb), 11)] += 1
        if len(Yb) > 5:
            stats['big'] += 1
            continue
        c = certify(YG, Xb)
        if c:
            stats['certified'] += 1
            print('VIOLATION G_%d X0=%s g=%s rkM=%d rkX=%d rkY=%d cert=%s'
                  % (j, X0, g, rank(MG), len(Xb), len(Yb), c), flush=True)
    print('STATS G', j, seed, stats)


def selftest():
    """w19-fp-last1 Theorem 1: B=<b, a b^2 a^-1> (not malnormal), X=ker(B->S3), g=a."""
    Bg = ['b', 'abbA']
    BG = fold_graph(Bg)
    print('selftest: B malnormal?', malnormal(BG))
    rb, rc = cyc(3, (0, 1, 2)), cyc(3, (0, 1))
    e = tuple(range(3))
    path = {e: ''}
    order = [e]
    for x in order:
        for (lab, gi) in (('b', rb), ('c', rc)):
            y = pmul(x, gi)
            if y not in path:
                path[y] = path[x] + lab
                order.append(y)
    m = {'b': 'b', 'c': 'abbA'}

    def tr(w):
        return red(''.join(m[ch] for ch in w))
    words = []
    for x in order:
        for (lab, gi) in (('b', rb), ('c', rc)):
            y = pmul(x, gi)
            w = red(tr(path[x]) + m[lab] + inv(tr(path[y])))
            if w:
                words.append(w)
    XG = fold_graph(words)
    Xb = basis(XG)[1]
    print('selftest: rk X =', len(Xb), '(expect 7)')
    JG = fold_graph(Xb + ['a'])
    YG = intersect(JG, BG)
    print('selftest: rk J =', rank(JG), 'rk Y =', rank(YG))
    print('selftest: certificate:', certify(YG, Xb))


if __name__ == '__main__':
    if sys.argv[1] == 'selftest':
        selftest()
    elif sys.argv[1] == 'G1':
        main_G(1)
    elif sys.argv[1] == 'G2':
        main_G(2)
    else:
        main()
