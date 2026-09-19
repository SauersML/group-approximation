"""Scan the relations w_k = [c1, sigma^k c1 sigma^-k] of
scale-periodic-bs-chain-germ-representations-are-not-faithful over many scales,
for the affine control delta = 2x and for a non-affine doubling lift.
Prints, per scale, the number of sample points moved by w_k."""
from fractions import Fraction as Fr
import sys
from germs import affine_control, nonaffine


def scan(ch, name, scales, ks, samples=400):
    print(f"== {name}")
    lo = ch.X
    for _ in range(3):
        lo = ch.delta(lo)
    for n in range(scales):
        hi = ch.delta(lo)
        if n >= scales - 6 or n % 2 == 0:
            row = []
            for k in ks:
                moved = 0
                for i in range(samples):
                    x = lo + (hi - lo) * Fr(2 * i + 1, 2 * samples)
                    if ch.w(k, x) != x:
                        moved += 1
                row.append(f"k={k}:{moved}")
            print(f"scale {n+3:2d} [{float(lo):.4g},{float(hi):.4g}) " + " ".join(row))
            sys.stdout.flush()
        lo = hi


if __name__ == "__main__":
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    scan(affine_control(), "affine control delta=2x", S, [7, 8, 12])
    scan(nonaffine(), "non-affine delta (slopes 1,2,4)", S, [7, 8, 12])
