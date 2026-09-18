"""Kesten-margin collapse on the 4-regular tree (q = 3).

Q_n = <a,t | a^2, [a, t^k a t^-k], 1 <= k <= n> (virtually free, nonamenable)
converges to the lamplighter L = Z/2 wr Z.  For m <= n every word of length
2m that is trivial in L is trivial in Q_n, so rho(Q_n) >= p_2m(L)^(1/2m).
The tree node gives p_c(N_n;T) = s(rho(Q_n)), s decreasing in rho, so
0 < p_c(N_n;T) - 1/3 <= s(p_2m(L)^(1/2m)) - 1/3.

Walk: image of the uniform measure on {a, a^-1, t, t^-1}, i.e. a with
probability 1/2, t and t^-1 with probability 1/4 each.  Floating-point DP on
(position, lamp set).
"""

from math import sqrt

q = 3


def s_of_rho(r):
    """Smaller root of q s^2 - r(q+1) s + 1 = 0, i.e. (q+1) s/(1+q s^2) = 1/r."""
    disc = r * r * (q + 1) ** 2 - 4 * q
    return (r * (q + 1) - sqrt(disc)) / (2 * q)


def return_probs(M):
    dist = {(0, frozenset()): 1.0}
    out = {}
    for step in range(1, 2 * M + 1):
        rem = 2 * M - step
        new = {}
        for (x, lamps), pr in dist.items():
            moves = (((x, lamps ^ {x}), 0.5),
                     ((x + 1, lamps), 0.25),
                     ((x - 1, lamps), 0.25))
            for (y, l2), w in moves:
                if abs(y) + len(l2) > rem:
                    continue
                key = (y, frozenset(l2))
                new[key] = new.get(key, 0) + pr * w
        dist = new
        if step % 2 == 0:
            out[step // 2] = dist.get((0, frozenset()), 0.0)
    return out


def main(M=18):
    assert abs(s_of_rho(1.0) - 1 / q) < 1e-12
    assert s_of_rho(0.95) > s_of_rho(0.99) > s_of_rho(1.0)


    best = 0.0
    print(" m  p_2m(L)       rho(Q_n) >=   gap(N_n) <=   (valid for n >= m)")
    for m in range(1, M + 1):
        p = return_probs(m)[m]
        r = float(p) ** (1.0 / (2 * m))
        best = max(best, r)
        gap = s_of_rho(best) - 1 / q if best > 2 * sqrt(q) / (q + 1) else float("nan")
        print(f"{m:2d}  {float(p):.6e}  {best:.6f}      {gap:.6f}")
    for r in (0.999, 0.9999):
        print("rho", r, "gap", round(s_of_rho(r) - 1 / q, 8),
              "linear", round((q + 1) * (1 - r) / (q * (q - 1)), 8))


if __name__ == "__main__":
    main()
