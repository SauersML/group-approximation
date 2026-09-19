"""Support density of c1 = [tau, sigma] and local-translation test for tau,
per delta-scale, on a fine exact grid; non-affine doubling lift."""
from fractions import Fraction as Fr
import sys
from germs import nonaffine, affine_control


def run(ch, name, scales, samples):
    print(f"== {name}")
    lo = ch.X
    for _ in range(3):
        lo = ch.delta(lo)
    for n in range(scales):
        hi = ch.delta(lo)
        moved = 0
        nontrans = 0
        eps = Fr(1, 2 ** 40)
        for i in range(samples):
            x = lo + (hi - lo) * Fr(2 * i + 1, 2 * samples)
            if ch.c1(x) != x:
                moved += 1
            # tau is a local translation at x iff tau(x+eps)-tau(x) == eps
            # on both sides (eps far below every breakpoint gap in range)
            if ch.tau(x + eps) - ch.tau(x) != eps or ch.tau(x) - ch.tau(x - eps) != eps:
                nontrans += 1
        disp = ch.tau(lo) - lo
        print(f"scale {n+3:2d} len={float(hi-lo):.4g} tau-disp~{float(disp):.3g} "
              f"c1 moves {moved}/{samples}  tau non-translation at {nontrans}/{samples}")
        sys.stdout.flush()
        lo = hi


if __name__ == "__main__":
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    run(nonaffine(), "non-affine", S, N)
