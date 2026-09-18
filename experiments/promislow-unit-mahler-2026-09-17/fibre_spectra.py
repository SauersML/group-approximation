#!/usr/bin/env python3
"""Fibre spectra of Gardam's unit on the Promislow group P.

Z[P] is a free right Z[L]-module on the coset representatives 1, a, b, ab (L = <a^2, b^2, (ab)^2> = Z^3),
so left multiplication gives Z[P] -> M_4(Z[L]); evaluating at a character xi of L gives U(xi) in M_4(C).
For Gardam's unit alpha in Z[zeta_8][P] (research/artifacts/gardam-support-pair-gsp.py, s=t=zeta_8, and all
Galois conjugates s=t=zeta_8^k, k odd) this prints
  * a check that U_alpha(xi) U_beta(xi) = 1 at random xi,
  * max / mean of log|lambda| over random xi (spectral radius of the fibre),
  * a Monte Carlo estimate of m = int_{T^3} sum_i log+ |lambda_i(xi)| d xi (Mahler measure of the reduced
    characteristic polynomial, by Jensen),
  * the same numbers for trivial units (calibration: must be 0).
Run from anywhere; it locates the repository root two directories above this file.
"""
import os, sys, importlib.util, cmath, math, random, tempfile
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.environ.get("CAIRN_ROOT", os.path.abspath(os.path.join(HERE, "..", "..")))
GSP = os.path.join(ROOT, "research", "artifacts", "gardam-support-pair-gsp.py")
if not os.path.exists(GSP):
    GSP = "/home/user/group-approximation/research/artifacts/gardam-support-pair-gsp.py"
cwd = os.getcwd(); os.chdir(tempfile.mkdtemp()); sys.argv = ["gsp"]
spec = importlib.util.spec_from_file_location("gsp", GSP)
G = importlib.util.module_from_spec(spec)
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    spec.loader.exec_module(G)
os.chdir(cwd)

REPS = [G.E, G.a, G.b, G.w(G.a, G.b)]
def lin(g): return tuple(g[i][i] for i in range(3))
REPLIN = [lin(c) for c in REPS]
INVREPS = [G.inv(c) for c in REPS]

def cols(g):
    """for each j: (i, translation vector of c_i^-1 g c_j)"""
    out = []
    for j, c in enumerate(REPS):
        k = G.mul(g, c)
        i = REPLIN.index(lin(k))
        l = G.mul(INVREPS[i], k)
        assert lin(l) == (1, 1, 1)
        tau = tuple(l[r][3] for r in range(3))
        assert all(t % 2 == 0 for t in tau), tau
        out.append((i, tuple(t // 2 for t in tau)))
    return out

def to_complex(U, zeta):
    # coefficients dict (i,j)->int in Z[s,t]/(s^4+1,t^4+1); specialise s=t=zeta
    return {g: sum(m * zeta ** (i + j) for (i, j), m in c.items()) for g, c in U.items()}

def compile_elem(Uc):
    return [(coef, cols(g)) for g, coef in Uc.items()]

def fibre(comp, theta):
    M = np.zeros((4, 4), dtype=complex)
    for coef, cl in comp:
        for j, (i, tau) in enumerate(cl):
            M[i, j] += coef * cmath.exp(1j * (theta[0] * tau[0] + theta[1] * tau[1] + theta[2] * tau[2]))
    return M

def stats(comp, n=4000, seed=7):
    rng = random.Random(seed)
    mx, tot = 0.0, 0.0
    for _ in range(n):
        th = [rng.uniform(0, 2 * math.pi) for _ in range(3)]
        ev = np.linalg.eigvals(fibre(comp, th))
        lg = np.log(np.abs(ev))
        mx = max(mx, lg.max())
        tot += np.clip(lg, 0, None).sum()
    return mx, tot / n

if __name__ == "__main__":
    rng = random.Random(1)
    for k in (1, 3, 5, 7):
        z = cmath.exp(1j * math.pi * k / 4)
        A = compile_elem(to_complex(G.alpha, z)); B = compile_elem(to_complex(G.beta, z))
        err = 0.0
        for _ in range(20):
            th = [rng.uniform(0, 2 * math.pi) for _ in range(3)]
            err = max(err, np.abs(fibre(A, th) @ fibre(B, th) - np.eye(4)).max())
        mxA, mA = stats(A); mxB, mB = stats(B)
        print(f"zeta_8^{k}: |U_alpha U_beta - 1|max = {err:.2e} | alpha: max log|lam| = {mxA:.4f}, "
              f"m ~ {mA:.4f} | beta: max log|lam| = {mxB:.4f}, m ~ {mB:.4f}")
    for name, g in (("a", G.a), ("b", G.b), ("x", G.x), ("xyZ", G.w(G.x, G.y, G.Z)), ("a x z", G.w(G.a, G.x, G.z))):
        mx, m = stats(compile_elem({g: 1}), n=500)
        print(f"trivial unit {name}: max log|lam| = {mx:.2e}, m ~ {m:.2e}")
