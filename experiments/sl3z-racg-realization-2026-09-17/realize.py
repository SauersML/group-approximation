"""Numerical rank-3 reflection realizations of right-angled Coxeter groups W_Gamma.

s_v = I - alpha_v beta_v^T, beta_v.alpha_v = 2; edge uv <=> beta_u.alpha_v = beta_v.alpha_u = 0.
Expected dimension of the realization space mod PGL_3 is 4V - 8 - 2E = -8 chi(W_Gamma).
For each random start we solve by Levenberg-Marquardt, then report: residual, local dimension
(nullity of the Jacobian minus gauge), irreducibility (Burnside: algebra generated = M_3),
and the multiset of non-edge products a_uw a_wu.
"""
import sys, itertools, numpy as np
from scipy.optimize import least_squares
import graphs as G


def unpack(x, n):
    return x[:3 * n].reshape(n, 3), x[3 * n:].reshape(n, 3)


def resid(x, n, E):
    a, b = unpack(x, n)
    r = [b[v] @ a[v] - 2 for v in range(n)] + [a[v] @ a[v] - 1 for v in range(n)]
    for u, v in E:
        r += [b[u] @ a[v], b[v] @ a[u]]
    return np.array(r)


def jac_num(x, n, E, h=1e-7):
    f0 = resid(x, n, E); J = np.zeros((len(f0), len(x)))
    for i in range(len(x)):
        y = x.copy(); y[i] += h; J[:, i] = (resid(y, n, E) - f0) / h
    return J


def mats(x, n):
    a, b = unpack(x, n)
    return [np.eye(3) - np.outer(a[v], b[v]) for v in range(n)]


def algebra_dim(M):
    span = [np.eye(3).ravel()]; basis = np.array(span)
    frontier = [np.eye(3)]
    for _ in range(4):
        new = []
        for X in frontier:
            for S in M:
                Y = S @ X; cand = np.vstack([basis, Y.ravel()])
                if np.linalg.matrix_rank(cand, tol=1e-6) > basis.shape[0]:
                    basis = cand; new.append(Y)
        frontier = new
        if not new:
            break
    return basis.shape[0]


def run(name, n, E, starts=40, seed=1):
    rng = np.random.default_rng(seed)
    nonE = [(u, w) for u, w in itertools.combinations(range(n), 2) if (u, w) not in set(E) and (w, u) not in set(E)]
    print(f"== {name}: V={n} E={len(E)} girth={G.girth(n, E)} maxcommon={G.max_common(n, E)} chi={G.euler_racg(n, E)} expdim={4*n-8-2*len(E)}")
    stats = {}
    for t in range(starts):
        x0 = rng.normal(size=6 * n)
        sol = least_squares(resid, x0, args=(n, E), method='trf', xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=5000)
        res = np.linalg.norm(sol.fun)
        if res > 1e-8:
            stats['fail'] = stats.get('fail', 0) + 1; continue
        J = jac_num(sol.x, n, E)
        sv = np.linalg.svd(J, compute_uv=False)
        null = 6 * n - int(np.sum(sv > 1e-5))
        M = mats(sol.x, n); ad = algebra_dim(M)
        a, b = unpack(sol.x, n)
        prods = sorted(round(float((b[u] @ a[w]) * (b[w] @ a[u])), 4) for u, w in nonE)
        zeros = sum(1 for u, w in nonE if abs(b[u] @ a[w]) < 1e-6 and abs(b[w] @ a[u]) < 1e-6)
        key = (null, ad, zeros)
        stats[key] = stats.get(key, 0) + 1
        if stats[key] == 1:
            print(f"  nullity={null} (dim mod PGL3 ~ {null-8}) algebra_dim={ad} commuting_nonedges={zeros} prods[:8]={prods[:8]}")
    print("  summary:", stats)


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    cases = {
        'C5': G.cycle(5), 'C6': G.cycle(6), 'petersen': G.petersen(),
        'Q4': G.hypercube(4), 'C13_1_5': G.circulant(13, [1, 5]),
    }
    for k, (n, E) in cases.items():
        if which in ('all', k):
            run(k, n, E, starts=int(sys.argv[2]) if len(sys.argv) > 2 else 20)
