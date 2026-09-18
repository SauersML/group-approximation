"""Zero counts (argument principle) and growth of a_(n,R)(z) on T_3 box K_2."""
import sys
import numpy as np
from ladder_connectivity import a_nR

PC, P2, RHO = 0.3805530886, 0.5262004719, (2 * np.sqrt(2) + 1) / 4


def winding(vals):
    d = np.angle(vals[1:] / vals[:-1])
    return np.sum(d) / (2 * np.pi), np.max(np.abs(d))


def circle_count(n, R, c, rad, M=8192):
    t = np.linspace(0, 2 * np.pi, M + 1)
    z = c + rad * np.exp(1j * t)
    v = a_nR(z, n, R)
    w, jump = winding(v)
    return w, jump, np.max(np.abs(v)) ** (1 / n), np.min(np.abs(v)) ** (1 / n)


def box_count(n, R, x0, x1, y0, y1, M=800):
    s = np.linspace(0, 1, M, endpoint=False)
    z = np.concatenate([x0 + (x1 - x0) * s + 1j * y0, x1 + 1j * (y0 + (y1 - y0) * s),
                        x1 - (x1 - x0) * s + 1j * y1, x0 + 1j * (y1 - (y1 - y0) * s)])
    z = np.append(z, z[0])
    v = a_nR(z, n, R)
    return winding(v)


def part_circles():
    print("circles about p_c: n R rad | zeros inside, max arg jump, max|a|^(1/n), min|a|^(1/n)")
    for n in (20, 50, 100, 200, 400):
        for R in (n, n + 1, 2 * n, 8 * n):
            for rad in (0.08, 0.13):
                w, j, mx, mn = circle_count(n, R, PC, rad)
                print(f"  n={n:4d} R={R:5d} rad={rad:.2f} | {w:+.3f} jump={j:.3f}"
                      f" max^(1/n)={mx:.4f} min^(1/n)={mn:.4f}")


def part_map(n, R, h=0.05):
    print(f"zero map n={n} R={R}: boxes [x,x+h]x[y,y+h] with nonzero count")
    for x in np.arange(0.0, 1.0, h):
        for y in np.arange(-0.6, 0.6, h):
            w, j = box_count(n, R, x, x + h, y, y + h)
            if abs(w) > 0.5 or j > 1.5:
                print(f"  box x=[{x:.2f},{x+h:.2f}] y=[{y:+.2f},{y+h:+.2f}] zeros={w:+.2f} jump={j:.2f}")


if __name__ == "__main__":
    what = sys.argv[1]
    if what == "circles":
        part_circles()
    elif what == "map":
        part_map(int(sys.argv[2]), int(sys.argv[3]))
