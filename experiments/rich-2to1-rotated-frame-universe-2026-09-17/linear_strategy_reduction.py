"""Exact low-dimensional reduction of the linear strategy f(x)=argmax_a <x_a,u>
on the rotated-frame universe game U_n (ambient R^{2n}).

For right vertex y with complement basis d, write alpha_b=<y_b,u>, w = proj of u
onto span(d).  The neighbour coordinates are <x_{b,+-},u> = (alpha_b +- beta_b)/sqrt2
with beta = R^T w, i.e. |w| times a uniform unit vector of R^n, fresh per edge.
So f lands in pair b iff b = argmax_c alpha_c + |beta_c|, and
val_lin(n) = E_alpha max_b Pr_beta[b wins].
Held-out estimate (selection on half the beta samples, evaluation on the other).
"""
import sys

import numpy as np


def val_lin(n, ny=300, nr=4000, seed=1):
    rng = np.random.default_rng(seed)
    tot = 0.0
    for _ in range(ny):
        u = rng.standard_normal(2 * n)
        u /= np.linalg.norm(u)
        alpha, wn = u[:n], np.linalg.norm(u[n:])
        g = rng.standard_normal((nr, n))
        beta = wn * g / np.linalg.norm(g, axis=1, keepdims=True)
        win = np.argmax(alpha[None, :] + np.abs(beta), axis=1)
        c0 = np.bincount(win[0::2], minlength=n)
        c1 = np.bincount(win[1::2], minlength=n)
        tot += c1[np.argmax(c0)] / len(win[1::2])
    return tot / ny


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [4, 16, 64, 256, 1024]
    prev = None
    for n in ns:
        v = val_lin(n)
        slope = "" if prev is None else " local_exponent=%.3f" % (
            np.log(v / prev[1]) / np.log(n / prev[0]))
        print("n=%d val_lin=%.4f%s" % (n, v, slope), flush=True)
        prev = (n, v)
