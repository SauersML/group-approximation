"""Exact checks for coboundary-expanding-hosts-cannot-carry-shift-ugc.

For small weighted hosts G with a weighted cycle system C this computes, over Z_2:
  * M(C)  = max_e  sum_c mu_C(c) * mult_c(e) / mu_E(e)       (congestion ratio)
  * beta  = min over b not in B^1 of mu_C(nonflat b) / dist_{mu_E}(b, B^1)
  * lam2  = second smallest eigenvalue of the normalized Laplacian of (G, mu_E)
by brute force over all 2^|E| cochains and all 2^(|V|-1) gauges.
It also checks the YES-side inequality mu_C(nonflat) <= M * (violated weight)
on random left-shift games over the non-abelian group S_3 with a planted labeling.
"""
import itertools, random
import numpy as np


def lam2(V, edges, w):
    A = np.zeros((V, V))
    for (u, v), x in zip(edges, w):
        A[u, v] += x; A[v, u] += x
    d = A.sum(1); Dm = np.diag(1 / np.sqrt(d))
    L = np.eye(V) - Dm @ A @ Dm
    return sorted(np.linalg.eigvalsh(L))[1]


def analyse(name, V, edges, w, cycles, wc):
    E = len(edges); w = np.array(w, float); w /= w.sum()
    wc = np.array(wc, float); wc /= wc.sum()
    idx = {e: i for i, e in enumerate(edges)}
    Cm = np.zeros((len(cycles), E), int)
    for j, cyc in enumerate(cycles):
        for a, b in zip(cyc, cyc[1:] + cyc[:1]):
            Cm[j, idx[(a, b)] if (a, b) in idx else idx[(b, a)]] += 1
    marg = wc @ Cm
    M = max(marg[i] / w[i] for i in range(E))
    allb = np.array(list(itertools.product([0, 1], repeat=E)), np.int8)
    nonflat = ((allb @ Cm.T) % 2) @ wc
    dist = np.full(len(allb), np.inf)
    for x in itertools.product([0, 1], repeat=V - 1):
        x = (0,) + x
        dx = np.array([x[u] ^ x[v] for u, v in edges], np.int8)
        dist = np.minimum(dist, ((allb ^ dx) @ w))
    mask = dist > 1e-12
    beta = (nonflat[mask] / dist[mask]).min() if len(cycles) else 0.0
    print(f"{name:34s} |V|={V:2d} |E|={E:2d} lam2={lam2(V, edges, w):.4f} "
          f"M={M:.3f} beta={beta:.4f} M/beta={'inf' if beta == 0 else round(M / beta, 3)}")


def perm_mul(p, q):  # (p*q)(i) = p(q(i))
    return tuple(p[q[i]] for i in range(len(q)))


def perm_inv(p):
    r = [0] * len(p)
    for i, x in enumerate(p): r[x] = i
    return tuple(r)


def yes_check(V, edges, w, cycles, wc, trials=2000, seed=1):
    rng = random.Random(seed); S3 = list(itertools.permutations(range(3)))
    w = np.array(w, float); w /= w.sum(); wc = np.array(wc, float); wc /= wc.sum()
    idx = {e: i for i, e in enumerate(edges)}
    marg = np.zeros(len(edges))
    for c, cyc in zip(wc, cycles):
        for a, b in zip(cyc, cyc[1:] + cyc[:1]):
            marg[idx[(a, b)] if (a, b) in idx else idx[(b, a)]] += c
    M = max(marg / w); worst = 0.0
    for _ in range(trials):
        x = [rng.choice(S3) for _ in range(V)]
        p = rng.random()
        b = {}
        for (u, v) in edges:  # constraint x_v = b_e x_u
            b[(u, v)] = perm_mul(x[v], perm_inv(x[u])) if rng.random() > p else rng.choice(S3)
        viol = sum(wi for (u, v), wi in zip(edges, w) if b[(u, v)] != perm_mul(x[v], perm_inv(x[u])))
        nf = 0.0
        for c, cyc in zip(wc, cycles):
            h = tuple(range(3))
            for a, bb in zip(cyc, cyc[1:] + cyc[:1]):
                g = b[(a, bb)] if (a, bb) in b else perm_inv(b[(bb, a)])
                h = perm_mul(g, h)
            nf += c * (h != tuple(range(3)))
        worst = max(worst, nf - M * viol)
    print(f"S_3 YES-side check: max(nonflat - M*viol) over {trials} planted games = {worst:.2e} (must be <= 0)")


def kmk2(m):
    edges, cyc = [], []
    for s in (0, m):
        for i, j in itertools.combinations(range(m), 2): edges.append((s + i, s + j))
        for t in itertools.combinations(range(m), 3): cyc.append([s + t[0], s + t[1], s + t[2]])
    for i in range(m): edges.append((i, m + i))
    for i, j in itertools.combinations(range(m), 2): cyc.append([i, j, m + j, m + i])
    return 2 * m, edges, [1] * len(edges), cyc


def cone_two_triangles(eta):
    H = [(1, 2), (2, 3), (1, 3), (4, 5), (5, 6), (4, 6)]
    edges = H + [(0, v) for v in range(1, 7)]
    w = [(1 - eta) / 6] * 6 + [eta / 6] * 6
    cyc = [[0, u, v] for u, v in H]
    return 7, edges, w, cyc, [1] * 6


def cone_two_triangles_balanced(eta):
    """Same host; C = the two H-triangles plus the six apex triangles, weighted
    so that the C-marginal is proportional to mu_E (congestion ratio M = 3)."""
    V, edges, w, cyc, _ = cone_two_triangles(eta)
    cyc = cyc + [[1, 2, 3], [4, 5, 6]]
    gam, alp = eta / 2, 1 - eta - eta / 2
    return V, edges, w, cyc, [gam] * 6 + [3 * alp] * 2


def two_k4_bridge():
    edges, cyc = [], []
    for s in (0, 4):
        for i, j in itertools.combinations(range(4), 2): edges.append((s + i, s + j))
        for t in itertools.combinations(range(4), 3): cyc.append([s + t[0], s + t[1], s + t[2]])
    edges.append((3, 4))
    return 8, edges, [1] * len(edges), cyc


def petersen():
    edges = [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)] + \
            [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    return 10, edges, [1] * 15, []  # girth 5: no closed cycles of length <= 4


if __name__ == "__main__":
    V, e, w, c = kmk2(4); analyse("K4 x K2, triangles+squares", V, e, w, c, [1] * len(c))
    V, e, w, c = two_k4_bridge(); analyse("two K4 + bridge, triangles", V, e, w, c, [1] * len(c))
    for eta in (0.2, 0.05, 0.01):
        V, e, w, c, wc = cone_two_triangles(eta)
        analyse(f"cone(K3+K3), apex weight {eta}", V, e, w, c, wc)
        V, e, w, c, wc = cone_two_triangles_balanced(eta)
        analyse(f"  same, balanced C (+H-triangles)", V, e, w, c, wc)
    V, e, w, c = petersen(); analyse("Petersen, cycles of length <= 4", V, e, w, c, [])
    V, e, w, c = kmk2(4); yes_check(V, e, w, c, [1] * len(c))
    V, e, w, c, wc = cone_two_triangles(0.05); yes_check(V, e, w, c, wc, seed=2)
