"""Checks for fpbs-boundary-cocycle-heights-markov-rare.

Part 1 (exact, rationals): visual measure on T_d, d = 3, 4, 5.
  For |y| = n the law of Delta_zeta(o,y) = (d-1)^(-(n-2k)) is explicit
  (item 5 of fpbs-boundary-tilted-susceptibility-kernel-proof).
  (a) normalisation int Delta dnu = 1;
  (b) Markov tail nu(Delta >= M) <= 1/M at every atom M;
  (c) the upper delta-quantile height H_delta(y) <= log(1/delta);
  (d) the ball union bound nu(max_{B_n} Delta >= (d-1)^n) = 1 versus
      |B_n| (d-1)^(-n), which stays >= 1 and bounded: h = log gr is sharp.
Part 2 (numerical): Cauchy law on R with affine maps g(x) = 2^n x - m
  (item 6 of the same proof). Delta_zeta(o, g^(-1)) = 2^n f(g zeta)/f(zeta).
  Checks the Markov tail by quadrature for several (n, m, M).
"""
from fractions import Fraction as Fr
import math


def tree_law(d, n):
    """Return list of (Delta, prob) for |y| = n >= 1 on T_d."""
    q = d - 1
    out = []
    out.append((Fr(1, q ** n), Fr(q, d)))  # k = 0
    for j in range(1, n):
        out.append((Fr(q ** (2 * j), q ** n), Fr(d - 2, d * q ** j)))
    out.append((Fr(q ** n), Fr(1, d * q ** (n - 1))))  # k = n
    return out


def part1():
    print("Part 1: visual measure on T_d")
    for d in (3, 4, 5):
        q = d - 1
        for n in range(1, 13):
            law = tree_law(d, n)
            tot = sum(p for _, p in law)
            mean = sum(D * p for D, p in law)
            assert tot == 1, (d, n, tot)
            assert mean == 1, (d, n, mean)
            atoms = sorted(set(D for D, _ in law))
            worst = Fr(0)
            for M in atoms:
                tail = sum(p for D, p in law if D >= M)
                assert tail <= 1 / M, (d, n, M, tail)
                worst = max(worst, tail * M)
            # quantile heights
            for delta in (Fr(1, 2), Fr(1, 10), Fr(1, 100), Fr(1, 10 ** 4)):
                H = max(math.log(D) for D in atoms
                        if sum(p for DD, p in law if DD >= D) >= delta)
                assert H <= math.log(1 / delta) + 1e-12, (d, n, delta, H)
            if n in (1, 4, 8, 12):
                ball = 1 + sum(d * q ** (r - 1) for r in range(1, n + 1))
                ratio = Fr(ball, q ** n)
                print(f"  d={d} n={n:2d}: mean=1, max_M M*nu(D>=M)={float(worst):.4f} <= 1,"
                      f" |B_n|/(d-1)^n={float(ratio):.4f}")
    print("  all exact checks passed")


def part2():
    print("Part 2: Cauchy law, affine maps x -> 2^n x - m")
    f = lambda x: 1.0 / (math.pi * (1.0 + x * x))
    # quadrature via zeta = tan(u), u in (-pi/2, pi/2): dnu = du/pi
    N = 400000
    for n in (1, 3, 6, 10):
        for m in (0, 1, 5, 37):
            if m >= 2 ** n and m > 1:
                continue
            vals = []
            for i in range(N):
                u = -math.pi / 2 + (i + 0.5) * math.pi / N
                z = math.tan(u)
                gz = 2 ** n * z - m
                vals.append(2 ** n * f(gz) / f(z))
            mean = sum(vals) / N
            line = f"  n={n:2d} m={m:2d}: mean={mean:.5f}"
            for M in (2.0, 8.0, 2.0 ** n):
                tail = sum(1 for v in vals if v >= M) / N
                assert tail <= 1.0 / M + 1e-3, (n, m, M, tail)
                line += f"  M={M:g}: M*nu={M * tail:.4f}"
            assert abs(mean - 1.0) < 1e-2, (n, m, mean)
            print(line)
    print("  all numerical checks passed")


if __name__ == "__main__":
    part1()
    part2()
