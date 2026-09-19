"""Inspect a saved census optimum (U, theta): how the exact pair moves the base.

usage: python3 analyze.py opt_s05_N81.npz
Prints ||U-1||, ||[U,D]||, the operator norm of the Fourier-off-diagonal part
of U (U is Fourier-diagonal iff this is 0), and the position/Fourier spread
of the eigenvectors U e_j of the corrected base Z = U D U^*.
"""
import sys, math, numpy as np

d = np.load(sys.argv[1])
U, th, N, s = d["U"], d["theta"], int(d["N"]), float(d["s"])
j = np.arange(N)
w = np.exp(2j * np.pi * j / N)
D = np.diag(w)
F = np.exp(-2j * np.pi * np.outer(j, j) / N) / math.sqrt(N)   # columns f_m
op = lambda X: np.linalg.norm(X, 2)
print(f"N={N} s={s}")
print(f"||U-1||={op(U-np.eye(N)):.4f}  ||[U,D]||={op(U@D-D@U):.4f}  ||UDU*-D||={op(U@D@U.conj().T-D):.4f}")
UF = F.conj().T @ U @ F
off = UF - np.diag(np.diag(UF))
print(f"Fourier-off-diagonal part of U: ||.||={op(off):.4f}  (Frobenius share {np.linalg.norm(off)/np.linalg.norm(UF):.3f})")
# circular spread of |U_{ij}|^2 around i=j (position) and of Fourier profile
P = np.abs(U) ** 2
dist = (j[:, None] - j[None, :] + N // 2) % N - N // 2
spread = np.sqrt((P * dist ** 2).sum(0))
print(f"position spread of eigenvectors (sites): median {np.median(spread):.2f} max {spread.max():.2f} (N={N})")
Q = np.abs(F.conj().T @ U) ** 2      # Fourier profile of each eigenvector
ent = -(Q * np.log(Q + 1e-300)).sum(0)
print(f"Fourier entropy of eigenvectors: median {np.median(ent):.2f} vs max {math.log(N):.2f}")
ev = np.angle(np.linalg.eigvals(U))
print(f"spectrum of U: max |angle| {np.abs(ev).max():.3f}, share with |angle|>0.3: {(np.abs(ev)>0.3).mean():.3f}")
