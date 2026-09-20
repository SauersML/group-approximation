"""Enumerate monotone rules mu: L^2 -> L (window {0,1} over Z) fixing constants on small
connected posets L, keep the injective ones, and test the cover property (Claim C):
a single-site cover move changes the image at exactly one site, by a cover.
Run: python3 search_z.py [all]"""
import itertools, sys


def closure(n, rel):
    le = [[i == j for j in range(n)] for i in range(n)]
    for a, b in rel:
        le[a][b] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if le[i][k] and le[k][j]:
                    le[i][j] = True
    return le


POSETS = {
    'chain3': (3, [(0, 1), (1, 2)]),
    'V': (3, [(0, 1), (0, 2)]),
    'N': (4, [(0, 2), (1, 2), (1, 3)]),
    'crown22': (4, [(0, 2), (0, 3), (1, 2), (1, 3)]),
    'M2=2x2': (4, [(0, 1), (0, 2), (1, 3), (2, 3)]),
    'Y': (4, [(0, 1), (1, 2), (1, 3)]),
    'bot+3': (4, [(0, 1), (0, 2), (0, 3)]),
    'M3': (5, [(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (3, 4)]),
    'N5': (5, [(0, 1), (1, 2), (2, 4), (0, 3), (3, 4)]),
    'fence5': (5, [(0, 1), (2, 1), (2, 3), (4, 3)]),
    '2x3': (6, [(0, 1), (1, 2), (3, 4), (4, 5), (0, 3), (1, 4), (2, 5)]),
}


def monotone_rules(n, le):
    inputs = list(itertools.product(range(n), repeat=2))

    def ple(p, q):
        return le[p[0]][q[0]] and le[p[1]][q[1]]

    order = sorted(inputs, key=lambda p: sum(le[j][p[0]] + le[j][p[1]] for j in range(n)))
    mu, res = {}, []

    def ok(p, v):
        for q, w in mu.items():
            if ple(p, q) and not le[v][w]:
                return False
            if ple(q, p) and not le[w][v]:
                return False
        return True

    def bt(k):
        if k == len(order):
            res.append(dict(mu))
            return
        p = order[k]
        for v in ([p[0]] if p[0] == p[1] else range(n)):
            if ok(p, v):
                mu[p] = v
                bt(k + 1)
                del mu[p]

    bt(0)
    return res


def injective(n, m):
    V = [(u, v) for u in range(n) for v in range(n)]
    E = {x: [(a, b) for a in range(n) for b in range(n) if m[(x[0], a)] == m[(x[1], b)]] for x in V}
    R = {x: [] for x in V}
    for x in V:
        for y in E[x]:
            R[y].append(x)

    def core(adj):
        alive, ch = set(V), True
        while ch:
            ch = False
            for x in list(alive):
                if not any(y in alive for y in adj[x]):
                    alive.discard(x)
                    ch = True
        return alive

    f, b = core(E), core(R)
    return not any(x[0] != x[1] and x in f and x in b for x in V)


def run(name, n, rel):
    le = closure(n, rel)
    cover = [[le[a][b] and a != b and not any(le[a][c] and le[c][b] and c not in (a, b)
                                              for c in range(n)) for b in range(n)] for a in range(n)]
    res = monotone_rules(n, le)
    inj = [m for m in res if injective(n, m)]
    bad = 0
    for m in inj:
        for l, a, r in itertools.product(range(n), repeat=3):
            for b in range(n):
                if not cover[a][b]:
                    continue
                d = [(m[(l, a)], m[(l, b)]), (m[(a, r)], m[(b, r)])]
                diff = [(u, w) for u, w in d if u != w]
                if len(diff) != 1 or not cover[diff[0][0]][diff[0][1]]:
                    bad += 1
    print(f"{name}: monotone constant-fixing rules {len(res)}, injective {len(inj)}, "
          f"cover-property violations {bad}", flush=True)
    return inj


if __name__ == '__main__':
    for name, (n, rel) in POSETS.items():
        if n <= 5 or 'all' in sys.argv:
            run(name, n, rel)
