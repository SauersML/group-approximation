"""Sanity check for Step 4 of full-shift-far-reading-density-diagonal-pair-proof.

Builds the pair (x, x') on a finite window and counts:
  d = disagreeing radius-M centres in J,
  s = centres a in J where k_q(sigma^a x) != k_q(sigma^a x') for q = s_{U_{M'}}.
Expect d == 0 and s == N + 1 > |J|/2.
"""


def k_q(y, Mp):
    # y: dict index -> bit, viewed at centre 0. U = {y_-1=1, y_0=0, y_Mp=0}; sigma U = {z: z_-2=1, z_-1=0, z_{Mp-1}=0}
    if y(-1) == 1 and y(0) == 0 and y(Mp) == 0:
        return 1
    if y(-2) == 1 and y(-1) == 0 and y(Mp - 1) == 0:
        return -1
    return 0


def run(N, M, Mp):
    assert N % 2 == 0 and Mp >= 2 * N + M + 1
    lo, hi = -N - M - 2, Mp + N + 2
    x = {n: (1 if n % 2 else 0) for n in range(lo, hi + 1)}
    for n in range(Mp - N, Mp + N + 1):
        x[n] = n % 3 % 2  # arbitrary
    xp = dict(x)
    for n in range(Mp - N, Mp + N + 1):
        xp[n] = 1 - x[n]
    J = range(-N, N + 1)
    d = sum(any(x[a + i] != xp[a + i] for i in range(-M, M + 1)) for a in J)
    s = sum(k_q(lambda n: x[a + n], Mp) != k_q(lambda n: xp[a + n], Mp) for a in J)
    return d, s, len(J)


if __name__ == "__main__":
    for N, M in [(2, 1), (6, 3), (20, 5), (50, 10)]:
        Mp = 2 * N + M + 1
        d, s, L = run(N, M, Mp)
        print(f"N={N} M={M} M'={Mp}: d={d} s={s} |J|={L} ratio={s / L:.3f}")
        assert d == 0 and s >= N + 1
    print("ok")
