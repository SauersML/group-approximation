#!/usr/bin/env python3
"""Finite-window Rayleigh quotients of the size-only tree-stack test vector (floating point).

Test vector on S_n (pointed forests with n leaves, a subgraph of the Cayley graph of F by
model_check.py):  f(T_0..T_{m-1}; i) = y(T_i) prod_{j != i} x(T_j),
x(T) = u_{|T|} / sqrt(Cat(|T|-1)),  y(T) = v_{|T|} / sqrt(Cat(|T|-1)).
With p = u^2, q = v^2, B_s = u_s v_s, M_{k,l} = c_{k,l} v_k u_l v_{k+l}:

  Z_0 = 1, Z_m = sum_s p_s Z_{m-s};   G = Z * Z;
  <f,f>      = D_n   = sum_s q_s G_{n-s}
  <f, A_S f> = Num_n = 2 sum_j H_j G_{n-j},   H_j = sum_{s+t=j} B_s B_t + sum_{k+l=j} M_{k,l}.

Rayleigh_n = Num_n / D_n <= ||x0 + x0^-1 + x1 + x1^-1||, and Rayleigh_n -> R(u, v) as n -> oo.
`python3 window_dp.py brute` compares with a brute-force sum over S_n for n <= 8.
"""
import sys
import numpy as np
from scipy.signal import fftconvolve
from size_ansatz import setup, optimise, logcat


def coefficients(u, v, C):
    N = len(u) - 1
    p, q, B = u ** 2, v ** 2, u * v
    H = np.zeros(2 * N + 1)
    H[:2 * N + 1] += np.convolve(B, B)
    for k in range(1, N):
        l = np.arange(1, N - k + 1)
        np.add.at(H, k + l, C[k, l] * v[k] * u[l] * v[k + l])
    return p, q, H


def rayleigh(u, v, C, nmax):
    p, q, H = coefficients(u, v, C)
    N = len(u) - 1
    Z = np.zeros(nmax + 1)
    Z[0] = 1.0
    for m in range(1, nmax + 1):
        s = np.arange(1, min(m, N) + 1)
        Z[m] = np.dot(p[s], Z[m - s])
    G = fftconvolve(Z, Z)[:nmax + 1]
    D = np.convolve(q, G)[:nmax + 1]
    Num = 2 * np.convolve(H, G)[:nmax + 1]
    return Num, D


def brute(u, v, n):
    sys.path.insert(0, '../thompson-f-cogrowth-2026-09-17')
    from forest_window_scout import forests, trees
    from math import comb, sqrt

    def cat(m):
        return comb(2 * m, m) // (m + 1)

    def nleaves(t):
        return 1 if t == () else nleaves(t[0]) + nleaves(t[1])
    x = lambda t: u[nleaves(t)] / sqrt(cat(nleaves(t) - 1))
    y = lambda t: v[nleaves(t)] / sqrt(cat(nleaves(t) - 1))

    def f(st):
        fo, i = st
        r = y(fo[i])
        for j, t in enumerate(fo):
            if j != i:
                r *= x(t)
        return r
    from model_check import moves
    num = den = 0.0
    for fo in forests(n):
        for i in range(len(fo)):
            st = (fo, i)
            fs = f(st)
            den += fs * fs
            for g, y2 in moves(st):
                num += fs * f(y2)
    return num / den


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == 'brute':
        r, u, v = optimise(6)
        C = setup(6)
        Num, D = rayleigh(u, v, C, 8)
        u, v = np.pad(u, (0, 3)), np.pad(v, (0, 3))  # trees above the truncation get weight 0
        for n in range(2, 9):
            print(n, "dp", Num[n] / D[n], "brute", brute(u, v, n))
    else:
        N = int(sys.argv[1]) if len(sys.argv) > 1 else 80
        nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
        r, u, v = optimise(N)
        C = setup(N)
        Num, D = rayleigh(u, v, C, nmax)
        print(f"N={N} R_inf/4={r/4:.6f}")
        for n in [100, 300, 1000, 3000, 10000, 20000, 50000, 100000]:
            if n <= nmax:
                print(f"  n={n}: Rayleigh_n/4 = {Num[n]/D[n]/4:.6f}")
