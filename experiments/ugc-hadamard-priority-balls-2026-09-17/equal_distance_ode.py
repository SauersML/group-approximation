"""Necessary condition for the continuum priority-ball adversary to have value C:
along the equal-distance configurations (M pins at normalized distance s,
M <= (1-2s)^-2, and M >= 2 only for s >= 1/4), the profile g must satisfy
  -g'/2 <= min_M h_M(g),  h_M(g) = (C - (1-g)^M) g / (1 - (1-g)^M).
Integrate the fastest admissible descent from g(0) = 1; the adversary family
can reach value C only if g reaches 0 before s = 1/2.  Floating point.
"""
import sys
import numpy as np
POW4 = len(sys.argv) > 1 and sys.argv[1] in ("pow4", "m4")
M4ONLY = len(sys.argv) > 1 and sys.argv[1] == "m4"


def h(M, g, C):
    q = (1 - g) ** M
    return (C - q) * g / (1 - q) if g > 1e-12 else (C - 1) / M


def run(C, ds=2e-5):
    s, g = 0.0, 1.0
    while s < 0.5:
        Mm = 1 if s < 0.25 else int(np.floor(1 / (1 - 2 * s) ** 2 + 1e-12))
        if POW4 and Mm > 1:
            Mm = 4 if M4ONLY else 4 ** int(np.floor(np.log(float(Mm)) / np.log(4) + 1e-12))
        a = min(h(1, g, C), h(Mm, g, C))  # h_M is monotone in M
        g -= 2 * a * ds
        s += ds
        if g <= 0:
            return s
    return None


def threshold(lo=1.5, hi=2.6, it=24):
    """Least C for which the fastest admissible descent reaches 0 before 1/2."""
    for _ in range(it):
        mid = (lo + hi) / 2
        if run(mid, ds=5e-5) is None:
            lo = mid
        else:
            hi = mid
    return lo, hi, run(hi, ds=5e-5)


if __name__ == '__main__':
    print("threshold (pow4=%s):" % POW4, threshold())
