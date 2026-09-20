"""Product-threshold bubble adversary for the Hadamard gadget minimax R*(k).

Adversary P_g (profile g: {0..K} -> [0,1], g(0) = 1, g(e) = 0 for e >= K/2):
  draw i uniform in F_2^k, tau uniform in {+-1}, xi uniform in {+-1}^K,
  and independent thresholds u_a uniform in [0,1], one per character a.
  Bad set B = {a : xi_a != tau chi_a(i)}  (iid fair bits for fixed i, tau).
  e_a(x) = (K - x_i chi_a(i) W_a(x)) / 2  = distance from x to the signed
  pin of index a in the half-cube {z : z_i = x_i}.
  x in S  iff  some a in B has u_a < g(e_a(x));   P_g(x) = tau x_i (-1)^[x in S].
Folded (e_a(-x) = e_a(x)), random on pins (at sigma chi_a: e_a = 0, e_b = K/2).

Exact edge price (x, y = x^j), K Pr[cut] = 1 - D_j + sum_{i != j} D_i with
  D_i = Pr[exactly one of x, y in S | i]
      = prod(1 - gx/2) + prod(1 - gy/2) - 2 prod(1 - max(gx, gy)/2).
The price is invariant under AGL(k) on coordinates, x -> x chi_c and x -> -x,
so it suffices to price the RM(1,k)-coset orbit representatives.
"""
import sys
import numpy as np


def hadamard(k):
    K = 1 << k
    H = np.ones((K, K))
    for a in range(K):
        for z in range(K):
            if bin(a & z).count("1") % 2:
                H[a, z] = -1
    return H


def load_reps(k, path):
    K = 1 << k
    reps = []
    for line in open(path):
        h, sz = line.split()
        f = int(h, 16)
        x = np.array([-1.0 if (f >> z) & 1 else 1.0 for z in range(K)])
        reps.append((x, int(sz)))
    return reps


def edge_prices(x, H, g):
    """Return array over j of K Pr[cut (x, x^j)] for profile g (length K+1)."""
    K = len(x)
    W = H @ x
    out = np.empty(K)
    # e[i, a] for x
    ex = ((K - x[:, None] * H.T * W[None, :]) / 2).astype(int)
    gx = g[ex]
    Px = np.prod(1 - gx / 2, axis=1)
    for j in range(K):
        y = x.copy(); y[j] = -y[j]
        Wy = W - 2 * x[j] * H[:, j]
        ey = ((K - y[:, None] * H.T * Wy[None, :]) / 2).astype(int)
        gy = g[ey]
        Py = np.prod(1 - gy / 2, axis=1)
        Pb = np.prod(1 - np.maximum(gx, gy) / 2, axis=1)
        D = Px + Py - 2 * Pb
        out[j] = 1 - D[j] + (D.sum() - D[j])
    return out


def all_prices(reps, H, g):
    return np.concatenate([edge_prices(x, H, g) for x, _ in reps])


def linear_profile(K, s0=0.5, theta=0.0):
    e = np.arange(K + 1)
    g = np.clip(1 - e / (s0 * K), 0, 1)
    g[e >= K // 2] = 0
    return g


if __name__ == "__main__":
    k = int(sys.argv[1])
    K = 1 << k
    H = hadamard(k)
    reps = load_reps(k, f"reps_k{k}.txt")
    for s0 in (0.25, 0.3, 0.35, 0.4, 0.45, 0.5):
        g = linear_profile(K, s0)
        p = all_prices(reps, H, g)
        print(f"k={k} s0={s0}: max price {p.max():.6f}")
