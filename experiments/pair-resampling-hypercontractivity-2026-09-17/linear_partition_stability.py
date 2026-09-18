"""Monte Carlo partition stability Stab_T(S) = Pr[A(X) = A(X'')] of the
linear equivariant partition A(X) = argmax_a <x_a, w> under the pair-resampling
operator T = E_P E[. | Pi_P X] on the rotated-frame universe (d = 2n).

Only g = X w matters: g is uniform on S^(2n-1); X'' w keeps the pair sums
(g_a + g_a')/sqrt2 and replaces the difference vector (g_a - g_a')/sqrt2 in R^n
by M times it, M Haar in O(n), i.e. by a uniform vector of the same norm.
Also reports the planted value E max_a p_a of the linear strategy pair
(A, B(Y) = argmax_b <y_b, w>)."""
import numpy as np

rng = np.random.default_rng(20260918)


def trial(n, T):
    N = 2 * n
    g = rng.standard_normal((T, N))
    g /= np.linalg.norm(g, axis=1, keepdims=True)
    a = g.argmax(axis=1)
    # random pairing: random permutation, pairs (perm[2i], perm[2i+1])
    perm = np.argsort(rng.random((T, N)), axis=1)
    gp = np.take_along_axis(g, perm, axis=1)
    y = (gp[:, 0::2] + gp[:, 1::2]) / np.sqrt(2)
    z = (gp[:, 0::2] - gp[:, 1::2]) / np.sqrt(2)
    r = np.linalg.norm(z, axis=1, keepdims=True)
    u = rng.standard_normal((T, n))
    z2 = u / np.linalg.norm(u, axis=1, keepdims=True) * r
    gp2 = np.empty_like(gp)
    gp2[:, 0::2] = (y + z2) / np.sqrt(2)
    gp2[:, 1::2] = (y - z2) / np.sqrt(2)
    g2 = np.empty_like(g)
    np.put_along_axis(g2, perm, gp2, axis=1)
    a2 = g2.argmax(axis=1)
    stab = np.mean(a == a2)
    # linear strategy value: B picks argmax pair sum
    b = y.argmax(axis=1)
    pos = np.argsort(perm, axis=1)  # position of label in perm
    pa = np.take_along_axis(pos, a[:, None], axis=1)[:, 0] // 2
    val = np.mean(pa == b)
    return stab, val


if __name__ == '__main__':
    print("n  Stab_T(linear)  2n*Stab-scaled  val_linear  (2n)^(-1/3)  (2n)^(-0.1716)")
    for n in [4, 16, 64, 256, 1024]:
        T = 200000 if n <= 256 else 50000
        s, v = trial(n, T)
        print(f"{n:5d} {s:.5f} {v:.5f} {(2*n)**(-1/3):.5f} {(2*n)**(-0.1716):.5f}", flush=True)
