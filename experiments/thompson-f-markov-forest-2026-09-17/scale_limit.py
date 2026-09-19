#!/usr/bin/env python3
"""Scale limit (log M -> infinity) of the Markov size-chain test vectors of markov_ansatz.py.

Rescaled log-size y = log(n)/log(M) in [0,1].  In this limit merge acts as max on y, and a split of a
tree of rescaled size m gives one child of size m and one child of any size s <= m.  For a kernel with
densities f_a(.) and stationary density pi,

  B = int_0^1 dm sqrt( int_0^m ds [ G(s,m)^2 f_s(m) + pi(m)^2 f_m(s) H(s,m)^2 ] ),
  G(s,m) = int pi(a) sqrt(f_a(s) f_a(m)) da,   H(s,m) = BC(f_s, f_m).

(first term: left child small; second: right child small.)  Product kernels give exactly 2 sqrt(2)/3.
Here f is piecewise constant on N bins (K[i,j] = bin transition probabilities); the bin-level formula
is exact for such kernels:  B = sum_J int_0^1 sqrt(A_J + t c_JJ) dt,  A_J = sum_{I<J} c_IJ,
c_IJ = g_IJ^2 K_IJ + pi_J^2 K_JI h_IJ^2,  g = S^T diag(pi) S,  h = S S^T,  S = sqrt(K).
"""
import sys
import torch
from markov_ansatz import stationary, opt

torch.set_default_dtype(torch.float64)


def scale_B(K):
    N = K.shape[0]
    pi = stationary(K)
    S = torch.sqrt(K)
    g = S.T @ (pi.unsqueeze(1) * S)
    h = S @ S.T
    c = g ** 2 * K + (pi ** 2).unsqueeze(0) * K.T * h ** 2      # c[I,J]
    low = torch.triu(torch.ones(N, N), diagonal=1)             # I < J
    A = (c * low).sum(0)
    d = torch.diagonal(c)
    return ((2.0 / 3.0) * ((A + d) ** 1.5 - A ** 1.5) / d).sum()


if __name__ == "__main__":
    torch.manual_seed(0)
    for N in [int(a) for a in sys.argv[1:]] or [4, 8, 16, 32]:
        best = -1
        for trial in range(4):
            L0 = 0.5 * trial * torch.randn(N, N)
            v, L = opt(lambda z: scale_B(torch.softmax(z, 1)), L0, iters=3000)
            best = max(best, v)
            print("N=%d trial %d  B=%.6f  R=(1+B)/2=%.6f" % (N, trial, v, (1 + v) / 2), flush=True)
        print("N=%d best B=%.6f (product 2sqrt2/3=%.6f)" % (N, best, 2 * 2 ** 0.5 / 3), flush=True)
