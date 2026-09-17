"""Small graph utilities (no networkx)."""
import random, itertools


def cycle(n):
    return n, [(i, (i + 1) % n) for i in range(n)]


def petersen():
    E = [(i, (i + 1) % 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)]
    return 10, E


def circulant(n, S):
    E = set()
    for i in range(n):
        for s in S:
            E.add(tuple(sorted((i, (i + s) % n))))
    return n, sorted(E)


def hypercube(d):
    n = 2 ** d
    return n, [(i, i ^ (1 << k)) for i in range(n) for k in range(d) if i < i ^ (1 << k)]


def adj(n, E):
    A = [set() for _ in range(n)]
    for u, v in E:
        A[u].add(v); A[v].add(u)
    return A


def girth(n, E):
    A = adj(n, E); g = 10 ** 9
    for s in range(n):
        dist = {s: 0}; par = {s: -1}; q = [s]
        for x in q:
            for y in A[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1; par[y] = x; q.append(y)
                elif par[x] != y:
                    g = min(g, dist[x] + dist[y] + 1)
    return g


def max_common(n, E):
    A = adj(n, E)
    return max(len(A[u] & A[v]) for u, v in itertools.combinations(range(n), 2))


def euler_racg(n, E):
    return 1 - n / 2 + len(E) / 4


def random_girth5(n, deg=4, tries=2000, seed=0):
    """Random greedy 4-regular girth>=5 graph; returns best found."""
    rng = random.Random(seed); best = None
    for _ in range(tries):
        A = [set() for _ in range(n)]; E = []
        pairs = list(itertools.combinations(range(n), 2)); rng.shuffle(pairs)
        for u, v in pairs:
            if len(A[u]) >= deg or len(A[v]) >= deg:
                continue
            # distance(u,v) >= 4 required so that adding uv creates no cycle of length <= 4
            near = {u}; fr = {u}
            for _ in range(3):
                fr = set().union(*[A[x] for x in fr]) - near if fr else set(); near |= fr
            if v in near:
                continue
            A[u].add(v); A[v].add(u); E.append((u, v))
        if best is None or len(E) > len(best):
            best = E
        if len(E) == n * deg // 2:
            break
    return n, sorted(best)
