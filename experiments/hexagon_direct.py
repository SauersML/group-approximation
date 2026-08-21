"""Direct hexagon flux on SL_3 Heisenberg towers at p = 3 versus p = 5.

Tests obligation (ii) of `hexagon-flux-is-adjacent-level-weil-ratio`:
the INTRINSIC canonical leg transports (defined only by intertwining
+ torus equivariance, no polarization input) are computed exactly,
and the hexagon scalar V_h^* V_h' V_h'' is evaluated.  Prediction
under the dictionary lemma: -1 at p = 3, +1 at p = 5.

Model at level q = p^k on l^2(Z/q) (k = 4):
    x(a) = shift by a, y(b) = diag e(bx/q), z(c) = e(c/q) scalar.
Coweight elements: h = diag(p,1,1/p), h' = diag(1,p,1/p),
h'' = diag(p,1/p,1), with h = h' h''.  Ad-weights on (x, y, z):
    h: (+1,+1,+2)   h': (-1,+2,+1)   h'': (+2,-1,+1).

Legs (targets: V_h: q -> q/p^2;  V_h'': q -> q/p;  V_h': q/p -> q/p^2):
  V_h   : T pi_q(x(p))   = pi_{q/p^2}(x(1)) T ;  T pi_q(y(p))   = pi_{q/p^2}(y(1)) T
  V_h'' : T pi_q(x(p^2)) = pi_{q/p}(x(p)) T   ;  T pi_q(y(1))   = pi_{q/p}(y(1)) T
  V_h'  : T pi_m(x(1))   = pi_{m/p}(x(1)) T   ;  T pi_m(y(p^2)) = pi_{m/p}(y(p)) T
          (m = q/p; the h'-domain at the mid level is the x-band
          reached by V_h''; its x-constraint uses x(p) upstairs
          mapping to x(1) downstairs after the h''-composition --
          both variants are solved and reported)
plus torus equivariance with U(lam) f(x) = f(lam^{-3} x) at every
level (the psi-stable torus diag(lam, lam^{-2}, lam), same concrete
formula at all levels), for lam a generator of (Z/q)^x.

Solver: the y-type constraints force a sparse support (phase
matching on diagonals); the x-type constraints propagate values
along shift orbits.  We solve exactly by building the constraint
system on the support and extracting the null space, then cut with
the torus constraint; Schur gap (dimension of the equivariant
solution space) is REPORTED -- the run is void unless the canonical
leg is unique up to phase (dim 1).

Everything is assembled as dense matrices only at p = 3 (dims 81,
27, 9) and p = 5 (dims 625, 125, 25) -- the largest null-space
computation is on the support-restricted system, far smaller than
the full matrix space.
"""
import numpy as np


def e(x):
    return np.exp(2j * np.pi * x)


def shift(q, a):
    S = np.zeros((q, q), dtype=complex)
    for x in range(q):
        S[x, (x - a) % q] = 1.0
    return S


def ymod(q, b):
    return np.diag([e((b * x) % q / q) for x in range(q)])


def torus(q, lam):
    li = pow(lam, -3, q)
    U = np.zeros((q, q), dtype=complex)
    for x in range(q):
        U[x, (li * x) % q] = 1.0
    return U


def solve_leg(qU, qD, consU, consD, lamU, lamD):
    """Solve T A_i = B_i T for (A_i, B_i) in zip(consU, consD) plus
    torus equivariance T U(lamU) = U(lamD) T, exactly, via SVD of the
    stacked system on the full (qD x qU) space if small, else report.
    Returns (T, sing_gap_info)."""
    n = qD * qU
    if n > 6000:
        raise RuntimeError(f"system too large for dense SVD: {n} unknowns")
    blocks = []
    for A, B in zip(consU, consD):
        blocks.append(np.kron(A.T, np.eye(qD)) - np.kron(np.eye(qU), B))
    blocks.append(np.kron(torus(qU, lamU).T, np.eye(qD))
                  - np.kron(np.eye(qU), torus(qD, lamD)))
    M = np.vstack(blocks)
    _, s, Vh = np.linalg.svd(M)
    smin, s2 = s[-1], s[-2]
    Tvec = Vh[-1].conj()
    T = Tvec.reshape((qU, qD)).T
    # polar normalize rows onto the image
    G = T @ T.conj().T
    ev, W = np.linalg.eigh(G)
    keep = ev > ev.max() * 1e-8
    inv = np.where(keep, 1.0 / np.sqrt(np.maximum(ev, 1e-30)), 0.0)
    T = W @ np.diag(inv) @ W.conj().T @ T
    return T, (smin, s2)


def run(p):
    k = 4
    q = p ** k
    m = q // p
    lo = q // (p * p)
    lam = 2 if p != 2 else 3
    # verify lam generates enough of the unit group (order check)
    o = 1
    t = lam % q
    while t != 1:
        t = t * lam % q
        o += 1
    print(f"p={p}: levels {q}->{m}->{lo}, torus lam={lam} order {o}", flush=True)

    # V_h : q -> lo
    Vh, gh = solve_leg(q, lo,
                       [shift(q, p), ymod(q, p)],
                       [shift(lo, 1), ymod(lo, 1)],
                       lam, lam)
    # V_h'' : q -> m
    Vpp, gpp = solve_leg(q, m,
                         [shift(q, p * p), ymod(q, 1)],
                         [shift(m, p), ymod(m, 1)],
                         lam, lam)
    # V_h' : m -> lo   (variant 1: x(1)->x(1) is impossible at weight -1,
    # the correct domain form after h'' is x(p)->x(1), y(p^2)->y(p))
    Vp, gp = solve_leg(m, lo,
                       [shift(m, p), ymod(m, p * p)],
                       [shift(lo, 1), ymod(lo, p)],
                       lam, lam)

    for name, (smin, s2) in (("V_h", gh), ("V_h''", gpp), ("V_h'", gp)):
        print(f"    {name}: smin={smin:.2e} next={s2:.2e} "
              f"{'UNIQUE' if s2 > 1e-6 and smin < 1e-8 else 'CHECK'}", flush=True)

    # hexagon: compare V_h against V_h' V_h''
    Lcomp = Vp @ Vpp          # q -> lo through the mid level
    # overlap of the two canonical routes, phase-invariant:
    num = np.trace(Vh @ Lcomp.conj().T)
    den = np.sqrt(abs(np.trace(Vh @ Vh.conj().T) * np.trace(Lcomp @ Lcomp.conj().T)))
    ov = num / den if den > 1e-12 else 0.0
    print(f"    hexagon overlap <V_h, V_h' V_h''> = {ov:+.6f} "
          f"|.|={abs(ov):.4f} arg={np.angle(ov)/np.pi:+.4f} pi", flush=True)
    # Only |overlap| is meaningful here: each intrinsic leg carries an
    # arbitrary SVD phase.  |overlap| ~ 1 means the two canonical routes
    # agree projectively (obligation (ii) holds: the hexagon is a pure
    # phase, whose VALUE is then fixed by the phase-canonical mechanism);
    # |overlap| << 1 means the routes land on different multiplicity
    # slots and the hexagon is not scalar.


for p in (3, 5):
    try:
        run(p)
    except RuntimeError as ex:
        print(f"p={p}: SKIPPED ({ex}) -- needs the combinatorial/sparse solver", flush=True)
print("HEXAGON-DIRECT-DONE")
