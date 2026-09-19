"""Sum-of-squares test for relative property (T) of (T-bar, <z>).

Since z is central, Delta_G and Delta_z = 2 - z - z^{-1} commute.  If
    Delta_G * Delta_z - lam * Delta_z  =  sum_i xi_i^* xi_i   in R[T-bar]
with lam > 0, then in every unitary representation Delta_G >= lam on the
orthogonal complement of the z-invariant vectors, i.e. (T-bar, <z>) has
relative property (T).  We maximise lam over Gram matrices P >= 0 indexed by
the ball B_R (xi supported on B_R).  Mode "T" instead tests
Delta_G^2 - lam * Delta_G (property (T) of T-bar itself; must give lam = 0,
since T-bar surjects onto the Haagerup group T).

usage: python sos.py R mode [gens]
   mode in {rel, T};  gens in {std, big}
"""
import sys, time
import numpy as np
import scipy.sparse as sp
import cvxpy as cp
from tbar import TBar, X0, X1, C, z, identity

ZZ = z()
C1 = C * ZZ.inv()          # C1^3 = z^{-1}
assert C1 ** 3 == ZZ.inv()


def gens(kind):
    base = [X0, X1, C1]
    if kind in ("withz", "bigz"):
        # z in the generating set, so Delta_G Delta_z is already SOS on B_2
        base = base + [ZZ]
    if kind in ("big", "bigz"):
        # add X0*X1^{-1} and C1*X0 to enlarge the generating set
        base = base + [X0 * X1.inv(), C1 * X0]
    S = []
    for g in base:
        S += [g, g.inv()]
    return S


def ball(S, R):
    e = identity()
    layers = [[e]]
    seen = {e: 0}
    for r in range(1, R + 1):
        new = []
        for g in layers[-1]:
            for s in S:
                h = g * s
                if h not in seen:
                    seen[h] = r
                    new.append(h)
        layers.append(new)
    return [g for L in layers for g in L], seen


def ring_mul(u, v):
    w = {}
    for g, a in u.items():
        for h, b in v.items():
            k = g * h
            w[k] = w.get(k, 0) + a * b
    return {k: c for k, c in w.items() if c != 0}


def main():
    R = int(sys.argv[1])
    mode = sys.argv[2]
    kind = sys.argv[3] if len(sys.argv) > 3 else "std"
    S = gens(kind)
    t0 = time.time()
    B, dist = ball(S, R)
    n = len(B)
    print("R=%d |S|=%d |B_R|=%d  (%.1fs)" % (R, len(S), n, time.time() - t0), flush=True)
    e = identity()
    DG = {e: len(S)}
    for s in S:
        DG[s] = DG.get(s, 0) - 1
    Dz = {e: 2, ZZ: -1, ZZ.inv(): -1}
    if mode == "rel":
        A0 = ring_mul(DG, Dz)   # Delta_G Delta_z
        A1 = Dz                  # coefficient of lam
    else:
        A0 = ring_mul(DG, DG)
        A1 = DG
    # index products x^{-1} y
    Binv = [g.inv() for g in B]
    idx = {}
    rows, cols = [], []
    for i in range(n):
        xi = Binv[i]
        for j in range(n):
            g = xi * B[j]
            k = idx.get(g)
            if k is None:
                k = idx[g] = len(idx)
            rows.append(k)
            cols.append(i + n * j)
    m = len(idx)
    print("support |B^-1 B| = %d  (%.1fs)" % (m, time.time() - t0), flush=True)
    for g in list(A0) + list(A1):
        if g not in idx:
            print("target not supported on B^-1 B; increase R")
            return
    Amat = sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(m, n * n))
    c0 = np.zeros(m)
    c1 = np.zeros(m)
    for g, a in A0.items():
        c0[idx[g]] = a
    for g, a in A1.items():
        c1[idx[g]] = a
    # keep one representative of each pair {g, g^{-1}} (constraints coincide for symmetric P)
    keep = []
    seen = set()
    for g, k in idx.items():
        if k in seen:
            continue
        seen.add(k)
        ki = idx.get(g.inv())
        if ki is not None:
            seen.add(ki)
        keep.append(k)
    keep = np.array(sorted(keep))
    Amat = Amat[keep]
    c0 = c0[keep]
    c1 = c1[keep]
    P = cp.Variable((n, n), symmetric=True)
    lam = cp.Variable()
    cons = [P >> 0, Amat @ cp.vec(P, order="F") == c0 - lam * c1]
    prob = cp.Problem(cp.Maximize(lam), cons + [lam <= 10])
    solver = sys.argv[4] if len(sys.argv) > 4 else "SCS"
    kw = dict(eps=1e-8, max_iters=200000) if solver == "SCS" else {}
    prob.solve(solver=solver, verbose=False, **kw)
    print("status", prob.status, " lam* =", lam.value, " (%.1fs)" % (time.time() - t0))
    if P.value is not None:
        ev = np.linalg.eigvalsh(P.value)
        print("min eig P = %.3e  max eig P = %.3e" % (ev[0], ev[-1]))
        # residual after projecting P onto the PSD cone (what a rigorous check would use)
        w, U = np.linalg.eigh(P.value)
        Pp = (U * np.clip(w, 0, None)) @ U.T
        res = Amat @ Pp.reshape(-1, order="F") - (c0 - lam.value * c1)
        print("l1 residual of PSD-projected Gram matrix = %.3e" % np.abs(res).sum())
        # trace of the image in R[T] (z -> 1): must vanish for an exact certificate
        print("trace(P) = %.4f" % np.trace(P.value))


if __name__ == "__main__":
    main()
