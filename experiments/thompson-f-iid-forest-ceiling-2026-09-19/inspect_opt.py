#!/usr/bin/env python3
"""Print the optimiser's size laws on a log grid, as k*alpha_k and k*beta_k (scouting)."""
import sys
import numpy as np
from size_law_problem import unpack, J_and_grad

N = int(sys.argv[1])
z = np.load(f"opt_N{N}.npy")
a, b = unpack(z, N)
al, be = a * a, b * b
k = np.arange(1, N + 1)
print(f"N={N} R={J_and_grad(a, b)[0]/4:.7f}")
print("   k    k*alpha_k*lnN   k*beta_k*lnN   cdfA   cdfB")
A, B = np.cumsum(al), np.cumsum(be)
L = np.log(N)
for kk in sorted(set([1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 600, 630, N])):
    if kk <= N:
        i = kk - 1
        print(f"{kk:5d}   {kk*al[i]*L:10.4f}   {kk*be[i]*L:10.4f}   {A[i]:.4f}  {B[i]:.4f}")
