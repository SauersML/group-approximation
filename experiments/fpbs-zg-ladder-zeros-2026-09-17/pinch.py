"""Where do the zeros of a_n pinch the real axis?  And the real rate lambda(p).

Part 1: zeros of a_(n,2n) in the strip x in [0.40,0.70], 0<y<0.20 (fine boxes)
for growing n: report the lowest zero (smallest Im) per n.
Part 2: log(a_(2n)/a_n)/n at real p versus log rho, around p_c and p_2.
Part 3: escape locus of the gadget map g -> 1-(1-z)(1-z^2 g)^2 from g=0
(sup_R |a_(n,R)| is infinite outside it), sampled on a grid.
"""
import numpy as np
from ladder_connectivity import a_nR
from zeros import box_count, PC, P2, RHO


def lowest_zero(n, h=0.01):
    best = None
    for x in np.arange(0.40, 0.70, h):
        for y in np.arange(0.0, 0.20, h):
            w, j = box_count(n, 2 * n, x, x + h, y + 1e-9, y + h, M=300)
            if abs(w) > 0.5 and (best is None or y < best[1]):
                best = (x, y, w)
    return best


def rate(p, n):
    z = np.array([p + 0j])
    a1 = a_nR(z, n, n + 1)[0].real
    a2 = a_nR(z, 2 * n, 2 * n + 1)[0].real
    return np.exp(np.log(a2 / a1) / n)


def escapes(z, iters=3000):
    g = 0 * z
    with np.errstate(all="ignore"):
        for _ in range(iters):
            g = 1 - (1 - z) * (1 - z * z * g) ** 2
            g = np.where(np.abs(g) > 1e6, 1e6, g)
    return np.abs(g) >= 1e6


if __name__ == "__main__":
    print(f"p_c={PC:.4f} p_2={P2:.4f} rho={RHO:.6f}")
    print("Part 1: lowest zero box (x,y) in strip, per n")
    for n in (100, 200, 400, 800):
        print(f"  n={n}: {lowest_zero(n)}")
    print("Part 2: rate estimate a_(2n)/a_n ^(1/n), n=400")
    for p in (0.30, PC, 0.45, 0.50, P2, 0.55, 0.60, 0.70):
        print(f"  p={p:.4f} rate={rate(p, 400):.6f}  (rho={RHO:.6f})")
    print("Part 3: escape locus; for each x, smallest |y| on a 0.005 grid that escapes")
    ys = np.arange(0.0, 1.5, 0.005)
    for x in np.arange(-0.2, 1.21, 0.1):
        e = escapes(x + 1j * ys)
        first = ys[np.argmax(e)] if e.any() else None
        print(f"  x={x:+.2f}: first escaping y = {first}")
