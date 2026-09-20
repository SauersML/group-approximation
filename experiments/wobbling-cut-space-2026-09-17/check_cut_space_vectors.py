"""Numerical check of the cut-space vectors used in
wobbling-relative-fh-displacement-ball-proof.

For a bijection g of Z with displacement <= r (supported on a finite window), a cut m
and a scale n, the unit vector xi = sqrt(mu) in l2(C) is the square root of the law of
A = [m, inf) xor E, with E having independent coordinates P(y in E) = p(y),
p(y) = theta(y - m)^2 / 2, theta(u) = clip(2 - |u|/n, 0, 1).

g_* mu is the law of [m, inf) xor E', E' independent with
P(y in E') = p(g^-1 y) if y not in D, 1 - p(g^-1 y) if y in D, D = g[m,inf) xor [m,inf).
Hence ||g xi - xi||^2 = 2 (1 - prod_y BC(p(y), p'(y))) exactly (finitely many
nontrivial coordinates).

Checks:
 (1) ||g xi - xi||^2 <= 4 r^2 / n whenever n >= 2r   (Step 2 of the route);
 (2) if g moves some z across m with |z - m| >= 2n and |gz - m| >= 2n, then
     ||g xi - xi||^2 = 2 exactly (Step 3).
"""
import math
import random


def theta(u, n):
    return min(1.0, max(0.0, 2.0 - abs(u) / n))


def p_of(y, m, n):
    return theta(y - m, n) ** 2 / 2.0


def bc(a, b):
    return math.sqrt(a * b) + math.sqrt((1 - a) * (1 - b))


def random_wobble(lo, hi, r, rng, swaps):
    """Random bijection of Z, identity outside [lo, hi], displacement <= r."""
    perm = {x: x for x in range(lo, hi + 1)}
    # compose random transpositions of span <= r on disjoint-ish blocks, then check
    for _ in range(swaps):
        x = rng.randint(lo, hi - 1)
        d = rng.randint(1, r)
        y = min(hi, x + d)
        # swap images of x and y if displacement stays <= r
        px, py = perm[x], perm[y]
        if abs(py - x) <= r and abs(px - y) <= r:
            perm[x], perm[y] = py, px
    return perm


def disp(perm):
    return max(abs(v - k) for k, v in perm.items())


def hellinger_sq(perm, m, n):
    """||g xi - xi||^2 for g = perm (identity off its window)."""
    inv = {v: k for k, v in perm.items()}
    g = lambda x: perm.get(x, x)
    ginv = lambda x: inv.get(x, x)
    window = set(range(m - 2 * n - 1, m + 2 * n + 2))
    window |= {g(y) for y in window} | {ginv(y) for y in window}
    window |= set(perm.keys())
    prod = 1.0
    for y in window:
        in_D = (g_in_half(ginv(y), m)) != (y >= m)
        q = p_of(ginv(y), m, n)
        pprime = 1 - q if in_D else q
        prod *= bc(p_of(y, m, n), pprime)
    return 2 * (1 - prod)


def g_in_half(x, m):
    # y in g[m, inf)  iff  g^-1 y >= m
    return x >= m


def main():
    rng = random.Random(20260917)
    worst = 0.0
    trials = 0
    for r in (1, 2, 3, 5):
        for n in (2 * r, 4 * r, 10 * r, 40 * r):
            for _ in range(60):
                m = rng.randint(-5, 5)
                perm = random_wobble(m - 3 * n, m + 3 * n, r, rng, 8 * n)
                rr = disp(perm)
                if rr == 0:
                    continue
                h = hellinger_sq(perm, m, n)
                bound = 4 * rr * rr / n
                assert n >= 2 * rr
                assert h <= bound + 1e-12, (r, n, h, bound)
                worst = max(worst, h / bound)
                trials += 1
    print(f"(1) upper bound ||g xi - xi||^2 <= 4 r^2 / n: {trials} trials, max ratio {worst:.4f}")

    # (2) a long transposition across the cut
    ok = 0
    for n in (3, 7, 20):
        for m in (-4, 0, 9):
            z = m - 2 * n
            w = m + 2 * n + rng.randint(0, 5)
            perm = {z: w, w: z}
            h = hellinger_sq(perm, m, n)
            assert abs(h - 2.0) < 1e-12, (n, m, h)
            ok += 1
            # a transposition that stays inside the zone is cheap, not singular
            perm2 = {m - 1: m + 1, m + 1: m - 1}
            assert hellinger_sq(perm2, m, n) < 2.0 - 1e-9
    print(f"(2) far crossing gives ||g xi - xi||^2 = 2 exactly: {ok} cases")


if __name__ == "__main__":
    main()
