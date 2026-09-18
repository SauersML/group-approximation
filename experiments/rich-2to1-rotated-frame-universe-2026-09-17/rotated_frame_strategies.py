"""Monte Carlo value estimates for potential-argmax strategies on the
rotated-frame universe rich 2-to-1 game U_n (ambient R^{2n}).

Right vertex: orthonormal y_1..y_n with complement basis d_1..d_n (Q Haar on O(2n)).
Neighbour left frame: x_{b,+-} = (y_b +- R d_b)/sqrt2, R Haar on O(n) acting on span(d).
Strategy: f(x) = argmax_a h(x_a), g(y) = argmax_b mu_b(y) (held-out estimate).
val_est = E_y mu_{g(y)}(y); selection and evaluation use disjoint R samples,
so the estimate is not inflated by max-of-noise.

Usage: python3 rotated_frame_strategies.py [n ...]
"""
import sys

import numpy as np


def haar(n, rng):
    z = rng.standard_normal((n, n))
    q, r = np.linalg.qr(z)
    return q * np.sign(np.diag(r))


def make_potentials(D, rng):
    u = rng.standard_normal(D)
    u /= np.linalg.norm(u)
    U = haar(D, rng)[:, :4]
    A = rng.standard_normal((D, D))
    A = (A + A.T) / 2
    return {
        "linear": lambda V: V @ u,
        "abs": lambda V: np.abs(V @ u),
        "l4_4dirs": lambda V: ((V @ U) ** 4).sum(-1),
        "linf_coords": lambda V: np.abs(V).max(-1),
        "l4_coords": lambda V: (V ** 4).sum(-1),
        "quadratic": lambda V: np.einsum("...i,ij,...j->...", V, A, V),
    }


def run(n, ny=200, nr=400, seed=0):
    rng = np.random.default_rng(seed)
    D = 2 * n
    pots = make_potentials(D, rng)
    tot = {k: 0.0 for k in pots}
    for _ in range(ny):
        Q = haar(D, rng)
        Y = Q[:, :n].T
        Dd = Q[:, n:].T
        counts = {k: np.zeros((2, n)) for k in pots}
        for t in range(nr):
            R = haar(n, rng)
            RD = R @ Dd
            X = np.concatenate([Y + RD, Y - RD]) / np.sqrt(2)
            for k, h in pots.items():
                a = int(np.argmax(h(X)))
                counts[k][t % 2, a % n] += 1
        for k in pots:
            b = int(np.argmax(counts[k][0]))
            tot[k] += counts[k][1, b] / (nr / 2)
    return {k: v / ny for k, v in tot.items()}


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [4, 8, 16, 32]
    for n in ns:
        r = run(n)
        print(n, "1/n=%.3f" % (1 / n),
              " ".join("%s=%.3f" % kv for kv in r.items()), flush=True)
