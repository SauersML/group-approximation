#!/usr/bin/env python3
"""Two-box baker example (p = 2, n = 2) for
research/piecewise-baker-torus-lifts-force-monomial-lamp-linear-parts.md.

A point of C^2 is (x, y), with x and y binary sequences (truncated to N digits here).
Boxes:
  V_0 = {x[0] = 0}, V_1 = {x[0] = 1}.
Local coordinates on either box: (x', y) with x' = x[1:].
Interleave: z = Theta(x', y), with z_d = x'[d] and z_{-d-1} = y[d] for d >= 0.
Lamp map phi : C^2 -> M^ = (F_2^2)^Z:
  on V_0: alpha_m = z_{1-2m}, beta_m = z_{2m}     (a homeomorphism V_0 -> M^)
  on V_1: alpha_m = z_{2m},   beta_m = z_{1-2m}   (= swap o phi_0)
Elements of 2V:
  g = local baker B^2 on V_0 and B^-2 on V_1, where B(a u, y) = (u, a y)
  s = flip x[0]
Checked on finite windows |m| <= W with random points:
  (1) phi o g = h o phi, where h(alpha, beta) = (sigma^-1 alpha, sigma beta)
  (2) phi o s = w o phi, where w(alpha, beta) = (beta, -alpha) = (beta, alpha) in char 2
  (3) the side rule: for m -> +infinity, which coordinate alpha_m and beta_m read on each box
      (alpha on the y-side and beta on the x-side on V_0, and the reverse on V_1). This is the
      local side split of Theorem S'': opposite sides, but the assignment flips between boxes.
  (4) the shear e_12(1)(alpha, beta) = (alpha, beta + alpha) violates the side rule of every
      box: its new beta_m for large m reads BOTH x deep and y deep digits.
"""
import random

N = 60   # digits kept per coordinate
W = 10   # window |m| <= W
TRIALS = 2000


def z_of(xp, y, k):
    return xp[k] if k >= 0 else y[-k - 1]


def phi(x, y):
    box, xp = x[0], x[1:]
    al, be = {}, {}
    for m in range(-W - 2, W + 3):
        a = z_of(xp, y, 1 - 2 * m)
        b = z_of(xp, y, 2 * m)
        if box == 0:
            al[m], be[m] = a, b
        else:
            al[m], be[m] = b, a
    return al, be


def baker(xp, y):          # B(a u, y) = (u, a y)
    return xp[1:] + [0], [xp[0]] + y[:-1]


def baker_inv(xp, y):      # B^-1(u, a y) = (a u, y)
    return [y[0]] + xp[:-1], y[1:] + [0]


def g(x, y):
    box, xp = x[0], x[1:]
    f = baker if box == 0 else baker_inv
    xp, y = f(*f(xp, y))
    return [box] + xp, y


def s(x, y):
    return [1 - x[0]] + x[1:], y


def rand_pt():
    return [random.randint(0, 1) for _ in range(N)], [random.randint(0, 1) for _ in range(N)]


def reads(box, which, m):
    """Which original coordinate ('x' or 'y') and digit the entry which_m reads on box."""
    k_alpha, k_beta = 1 - 2 * m, 2 * m
    k = (k_alpha if which == 'alpha' else k_beta) if box == 0 else \
        (k_beta if which == 'alpha' else k_alpha)
    return ('x', k + 1) if k >= 0 else ('y', -k - 1)


def main():
    random.seed(20260917)
    bad_h = bad_w = 0
    for _ in range(TRIALS):
        x, y = rand_pt()
        al, be = phi(x, y)
        al_g, be_g = phi(*g(x, y))
        for m in range(-W, W + 1):
            # h: alpha' = sigma^-1 alpha (alpha'_m = alpha_{m-1}), beta' = sigma beta
            if al_g[m] != al[m - 1] or be_g[m] != be[m + 1]:
                bad_h += 1
        al_s, be_s = phi(*s(x, y))
        for m in range(-W, W + 1):
            if al_s[m] != be[m] or be_s[m] != al[m]:
                bad_w += 1
    print(f"trials={TRIALS} window=|m|<={W}")
    print(f"(1) phi o g = h o phi   mismatches: {bad_h}")
    print(f"(2) phi o s = w o phi   mismatches: {bad_w}")
    # negative control: the global baker B^2 (same sign on both boxes) must NOT lift h
    bad_ctrl = 0
    for _ in range(200):
        x, y = rand_pt()
        box, xp = x[0], x[1:]
        xp2, y2 = baker(*baker(xp, y))
        al, be = phi(x, y)
        al_g, be_g = phi([box] + xp2, y2)
        if any(al_g[m] != al[m - 1] or be_g[m] != be[m + 1] for m in range(-W, W + 1)):
            bad_ctrl += 1
    print(f"    control: global B^2 fails to lift h on {bad_ctrl}/200 points (expect ~100, the V_1 ones)")
    print("(3) side rule at m = +8 (coordinate, digit):")
    for box in (0, 1):
        print(f"    box V_{box}: alpha_8 reads {reads(box, 'alpha', 8)}, "
              f"beta_8 reads {reads(box, 'beta', 8)}")
    print("(4) e_12(1): new beta_m = beta_m + alpha_m reads, at m = +8:")
    for box in (0, 1):
        print(f"    box V_{box}: {reads(box, 'beta', 8)} and {reads(box, 'alpha', 8)}"
              f"  -> both sides deep, violates the local side split")
    ok = bad_h == 0 and bad_w == 0
    print("RESULT:", "PASS" if ok else "FAIL")


if __name__ == "__main__":
    main()
