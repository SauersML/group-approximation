"""Window-packing obstruction for the web rank inequality of C_n^4, n = 13, 14, 19.

For every vertex set W of C_n^4 with |W| <= 7 (up to isomorphism of the induced graph)
this finds an explicit admissible C_W (moduli 1 + x^2 >= 1) and records its trace norm,
an upper bound on c(G[W]).  A fractional packing (sum_{W ni i} y_W <= 1) gives at most
sum y_W c(W) <= n * max_W c(W)/|W|, so the packing bound cannot reach sqrt3 (n - floor(n/5))
once every density c(W)/|W| is below sqrt3 (n - floor(n/5))/n.
Usage: cover.py MAXSIZE RESTARTS
"""
import sys, itertools, numpy as np, networkx as nx
from scipy.optimize import minimize

def web(n, k=4):
    return {(i, j) for i in range(n) for j in range(i + 1, n) if min(j - i, n - j + i) <= k}

def classes(maxs, ns=(13, 14, 19)):
    reps = {}
    for n in ns:
        E = web(n)
        for s in range(1, maxs + 1):
            for rest in itertools.combinations(range(1, n), s - 1):
                W = (0,) + rest
                G = nx.Graph(); G.add_nodes_from(range(s))
                G.add_edges_from((a, b) for a in range(s) for b in range(a + 1, s)
                                 if (W[a], W[b]) in E)
                h = nx.weisfeiler_lehman_graph_hash(G, iterations=4)
                lst = reps.setdefault((s, G.number_of_edges(), h), [])
                if not any(nx.is_isomorphic(G, H) for H, _ in lst):
                    lst.append((G, (n, W)))
    return [(G, src) for lst in reps.values() for G, src in lst]

def cmin(G, rest, seed=0):
    n = G.number_of_nodes(); E = list(G.edges()); m = len(E)
    if m == 0:
        return 0.0, None
    I = np.array([e[0] for e in E]); J = np.array([e[1] for e in E])
    def mat(x):
        C = np.zeros((n, n), complex); v = (1 + x[:m] ** 2) * np.exp(1j * x[m:])
        C[I, J] = v; C[J, I] = np.conj(v); return C
    f = lambda x: np.abs(np.linalg.eigvalsh(mat(x))).sum()
    rng = np.random.default_rng(seed); best = (1e9, None)
    for r in range(rest):
        x0 = np.concatenate([rng.normal(0, .3, m), rng.uniform(0, 2 * np.pi, m)])
        res = minimize(f, x0, method='BFGS', options={'maxiter': 2000, 'gtol': 1e-9})
        res = minimize(f, res.x, method='Nelder-Mead',
                       options={'maxiter': 8000, 'xatol': 1e-10, 'fatol': 1e-12})
        if res.fun < best[0]:
            best = (res.fun, res.x)
    C = mat(best[1]); mu = np.abs(C[I, J]).min()
    if mu < 1:
        C = C / mu          # rescale so that every edge modulus is >= 1
    assert np.allclose(C, C.conj().T) and np.all(np.abs(C[I, J]) >= 1)
    return float(np.abs(np.linalg.eigvalsh(C)).sum()), best[1]

if __name__ == "__main__":
    maxs, rest = int(sys.argv[1]), int(sys.argv[2])
    thr = {n: np.sqrt(3) * (n - n // 5) / n for n in (13, 14, 19)}
    print("density thresholds", {n: round(t, 5) for n, t in thr.items()}, flush=True)
    cl = classes(maxs)
    print("classes", len(cl), "by size",
          {s: sum(1 for G, _ in cl if G.number_of_nodes() == s) for s in range(1, maxs + 1)},
          flush=True)
    out = []
    for G, (n, W) in cl:
        c, x = cmin(G, rest)
        d = c / G.number_of_nodes()
        out.append((d, c, G.number_of_nodes(), G.number_of_edges(), n, W))
    out.sort(reverse=True)
    for d, c, s, m, n, W in out[:25]:
        print("density %.5f  c<=%.5f  |W|=%d  edges=%d  from C_%d^4 W=%s" % (d, c, s, m, n, W))
    for s in range(1, maxs + 1):
        ds = [o[0] for o in out if o[2] == s]
        print("size %d: max density %.5f" % (s, max(ds)))
    print("max density over |W|<=6: %.5f" % max(o[0] for o in out if o[2] <= 6))
