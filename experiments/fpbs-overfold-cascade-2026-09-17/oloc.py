"""(O-loc) lawful-yield test.

For a set P of k overfold seeds clustered in a ball of a large random level
Q x_R C_{j+1}, compute N = cl(P) /\ ker m (the lawful part of the closure) and
ell = least number of lawful seeds S with cl(S) >= N.  Candidate lawful seeds
are restricted to pairs inside N (so ell reported is an upper bound on the
true ell; a report ell <= k is therefore conclusive for that P).
(O-loc): ell <= k for every P.  (O-loc) for all finite P implies (O).

Usage: python3 oloc.py MODEL n k radius trials seed
"""
import itertools
import random
import sys


def load(path):
    tok = open(path).read().split()
    it = iter(tok)
    Vc, Vb, T = int(next(it)), int(next(it)), int(next(it))
    nb = [[int(next(it)) for _ in range(4)] for _ in range(Vc)]
    io = [int(next(it)) for _ in range(Vc)]
    types = [tuple(int(next(it)) for _ in range(5)) for _ in range(T)]
    return Vc, Vb, nb, io, types


class Lvl:
    def __init__(self, model, n, rng):
        self.Vc, self.Vb, self.cnb, self.io, self.types = model
        self.n = n
        PA = list(range(n))
        PB = list(range(n))
        rng.shuffle(PA)
        rng.shuffle(PB)
        IA = [0] * n
        IB = [0] * n
        for i in range(n):
            IA[PA[i]] = i
            IB[PB[i]] = i
        self.act = [PA, IA, PB, IB]

    def nbr(self, v, i):
        q, c = divmod(v, self.Vc)
        d = self.cnb[c][i]
        return -1 if d < 0 else self.act[i][q] * self.Vc + d

    def m(self, v):
        q, c = divmod(v, self.Vc)
        return (q, self.io[c])

    def ball(self, q0, r):
        seen = {q0}
        fr = [q0]
        for _ in range(r):
            nf = []
            for q in fr:
                for i in range(4):
                    p = self.act[i][q]
                    if p not in seen:
                        seen.add(p)
                        nf.append(p)
            fr = nf
        return sorted(seen)


def closure(L, pairs, cap=200000):
    """Fold closure of the given vertex pairs; dict union-find, local.
    Returns the nontrivial classes, or None past cap merges."""
    par = {}
    adj = {}

    def find(x):
        r = x
        while par.get(r, r) != r:
            r = par[r]
        while par.get(x, x) != r:
            nx = par[x]
            par[x] = r
            x = nx
        return r

    def nbrs(r):
        a = adj.get(r)
        return a if a is not None else [L.nbr(r, i) for i in range(4)]
    st = list(pairs)
    steps = 0
    while st:
        x, y = st.pop()
        x, y = find(x), find(y)
        if x == y:
            continue
        steps += 1
        if steps > cap:
            return None
        par[y] = x
        ax, ay = nbrs(x), nbrs(y)
        new = list(ax)
        for i in range(4):
            if ay[i] >= 0:
                if new[i] >= 0:
                    st.append((new[i], ay[i]))
                else:
                    new[i] = ay[i]
        adj[x] = new
        adj.pop(y, None)
    cls = {}
    for v in set(par) | set(par.values()):
        cls.setdefault(find(v), []).append(v)
    return [c for c in cls.values() if len(c) > 1]


def lawful_part(L, classes):
    """Groups of cl(P) /\\ ker m: classes split by m-value, size >= 2."""
    out = []
    for c in classes:
        g = {}
        for v in c:
            g.setdefault(L.m(v), []).append(v)
        out.extend(sorted(x) for x in g.values() if len(x) > 1)
    return out


def contains(L, S, groups):
    cl = closure(L, S)
    root = {}
    for i, c in enumerate(cl):
        for v in c:
            root[v] = i
    for g in groups:
        r = root.get(g[0], -1 - g[0])
        for v in g[1:]:
            if root.get(v, -1 - v) != r:
                return False
    return True


def rank(groups):
    return sum(len(g) - 1 for g in groups)


def min_lawful(L, groups, kmax):
    """Least s <= kmax with s lawful seeds (pairs inside groups) whose
    closure contains groups; returns kmax+1 if none found."""
    if not groups:
        return 0
    cand = []
    seen = set()
    for g in groups:
        for u, v in itertools.combinations(g, 2):
            cl = closure(L, [(u, v)])
            key = frozenset(frozenset(c) for c in cl)
            if key not in seen:
                seen.add(key)
                cand.append((u, v))
    for s in range(1, kmax + 1):
        for S in itertools.combinations(cand, s):
            if contains(L, list(S), groups):
                return s
    return kmax + 1


def main():
    path, n, k, r, trials, seed = sys.argv[1:7]
    n, k, r, trials = int(n), int(k), int(r), int(trials)
    nlaw = int(sys.argv[7]) if len(sys.argv) > 7 else 0
    rng = random.Random(int(seed))
    model = load(path)
    L = Lvl(model, n, rng)
    over = [t for t in L.types if not t[2]]
    lawt = [t for t in L.types if t[2]]
    hist = {}
    worst = None
    for tr in range(trials):
        q0 = rng.randrange(n)
        B = L.ball(q0, r)
        P = []
        for _ in range(k):
            q = rng.choice(B)
            c, d = rng.choice(over)[:2]
            P.append((q * L.Vc + c, q * L.Vc + d))
        for _ in range(nlaw):
            q = rng.choice(B)
            c, d = rng.choice(lawt)[:2]
            P.append((q * L.Vc + c, q * L.Vc + d))
        cl = closure(L, P)
        if cl is None:
            hist['cap'] = hist.get('cap', 0) + 1
            continue
        N = lawful_part(L, cl)
        ell = min_lawful(L, N, k + nlaw + 1)
        key = (ell - k - nlaw) if N else 'empty'
        hist[key] = hist.get(key, 0) + 1
        if N and (worst is None or ell - k - nlaw > worst[0]):
            worst = (ell - k - nlaw, rank(N), P)
    print('# model', path, 'n', n, 'k', k, 'lawful', nlaw, 'radius', r, 'trials', trials)
    print('hist ell-|P| (empty = no lawful part):', sorted(hist.items(), key=str))
    print('worst ell-|P|, rank N, P:', worst)


if __name__ == '__main__':
    main()
