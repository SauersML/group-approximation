"""Independent check of the hypotheses of Zaremsky's Theorem 3.1 (arXiv:2410.11993)
on Cayley graphs of RAAGs with standard generators, at the scales produced by
jensen-helly-graphs-have-contractible-rips-complexes-proof:
  t >= k(k+1),  r_t = kt/(k+1) + k/2  (distances are integers, so use floor).
For sets S containing e with diam S = t:
  (a) Y(S) = {y : d(y,s) <= r_t for all s in S} is nonempty;
  (b) some y0 in Y(S) has d(y0,y) <= t for all y in Y(S).
Shares no code with the solver scripts.  Usage: python3 crit_check.py GRAPH t trials seed
"""
import sys, random, itertools

GRAPHS = {
    'P4': (4, [(0, 1), (1, 2), (2, 3)]),
    'C5': (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
    'P5': (5, [(0, 1), (1, 2), (2, 3), (3, 4)]),
    'paw': (4, [(0, 1), (1, 2), (0, 2), (2, 3)]),  # triangle + pendant, k=3
}


def setup(name):
    n, E = GRAPHS[name]
    adj = [[False] * n for _ in range(n)]
    for a, b in E:
        adj[a][b] = adj[b][a] = True
    # clique number
    k = 0
    for m in range(1, n + 1):
        for C in itertools.combinations(range(n), m):
            if all(adj[a][b] for a, b in itertools.combinations(C, 2)):
                k = m
    return n, adj, k


def make_ops(n, adj):
    # letters: (gen, sign) encoded as 2*gen + (0 for +, 1 for -)
    def commute(x, y):
        gx, gy = x >> 1, y >> 1
        return gx == gy or adj[gx][gy]

    def inv(x):
        return x ^ 1

    def append(w, x):
        # w is a reduced word (list); return reduced word for w*x
        i = len(w) - 1
        while i >= 0:
            y = w[i]
            if y == inv(x):
                return w[:i] + w[i + 1:]
            if y == x or not commute(x, y):
                break
            i -= 1
        return w + [x]

    def reduce(word):
        w = []
        for x in word:
            w = append(w, x)
        return w

    def nf(w):
        # shortlex normal form of a reduced word
        w = list(w)
        out = []
        while w:
            best = None
            for i, x in enumerate(w):
                if all(commute(x, w[j]) and w[j] != x for j in range(i)):
                    if best is None or x < w[best]:
                        best = i
            out.append(w[best])
            del w[best]
        return tuple(out)

    def dist(g, h):
        winv = [inv(x) for x in reversed(g)]
        return len(reduce(winv + list(h)))

    return commute, inv, append, nf, dist


def ball(n, append, nf, R):
    start = ()
    seen = {start: 0}
    frontier = [start]
    for rad in range(1, R + 1):
        new = []
        for g in frontier:
            for x in range(2 * n):
                h = nf(append(list(g), x))
                if h not in seen:
                    seen[h] = rad
                    new.append(h)
        frontier = new
    return seen


def main():
    name = sys.argv[1]
    t = int(sys.argv[2])
    trials = int(sys.argv[3])
    seed = int(sys.argv[4])
    rng = random.Random(seed)
    n, adj, k = setup(name)
    commute, inv, append, nf, dist = make_ops(n, adj)
    r = (k * t) // (k + 1) + (k // 2) if k % 2 == 0 else int(k * t / (k + 1) + k / 2)
    r = int((k * t) / (k + 1) + k / 2 + 1e-9)
    assert t >= k * (k + 1), (t, k)
    B = ball(n, append, nf, t)
    byrad = {}
    for g, rad in B.items():
        byrad.setdefault(rad, []).append(g)
    Bt = list(B.keys())
    Br = [g for g, rad in B.items() if rad <= r]
    print(name, 'k', k, 't', t, 'r_t', r, '|B_t|', len(Bt), '|B_r|', len(Br), flush=True)
    stats = {'trials': 0, 'emptyY': 0, 'nocentre': 0, 'maxS': 0, 'minY': 10 ** 9}
    for tr in range(trials):
        # build S greedily: e, a far point at distance t, then random points keeping diam <= t
        far = rng.choice(byrad[t])
        S = [(), far]
        target = rng.randint(2, 12)
        mode = rng.random()
        attempts = 0
        while len(S) < target and attempts < 400:
            attempts += 1
            if mode < 0.5:
                rad = rng.choice([t - 1, t]) if t in byrad else t
                g = rng.choice(byrad[rad])
            else:
                g = rng.choice(Bt)
            if g in S:
                continue
            if all(dist(g, s) <= t for s in S):
                S.append(g)
        diam = max(dist(a, b) for a, b in itertools.combinations(S, 2))
        assert diam == t
        Y = [y for y in Br if all(dist(y, s) <= r for s in S)]
        stats['trials'] += 1
        stats['maxS'] = max(stats['maxS'], len(S))
        stats['minY'] = min(stats['minY'], len(Y))
        if not Y:
            stats['emptyY'] += 1
            print('EMPTY Y', S, flush=True)
            continue
        ok = False
        for y0 in Y:
            if all(dist(y0, y) <= t for y in Y):
                ok = True
                break
        if not ok:
            stats['nocentre'] += 1
            print('NO CENTRE', S, len(Y), flush=True)
    print(stats, flush=True)


if __name__ == '__main__':
    main()
