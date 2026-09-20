"""Tree calibration of the high-girth Kesten transfer (Corollary A).

On the free-group tree T_{2k} (q = 2k-1) every normal subgroup N of F_k is
free, hence residually solvable, and the Cayley graph has infinite girth.  So
Corollary A of fpbs-l2-gap-transfers-to-kesten-normal-gap predicts, for every
N with rho_Q <= 1 - eta,

    chi^N_s <= M = 1 + 3/eta^2   at   s0 = 1/q + eta/(4q).

Independent check via Grigorchuk's cogrowth formula
    chi^N_s = sum_{x in N} s^|x| = (1-s^2)/(1+q s^2) * G_Q(d s/(1+q s^2)),
with d = q+1 and G_Q(z) = sum_n p_n(e) z^n <= 1/(1 - rho_Q z) (p_n(e) <= rho^n).
On the tree tau_s(e,x) = s^|x|, so chi^N_s is exactly this cogrowth series.
The bound is uniform over all Q with rho_Q <= 1-eta, so the check covers every
normal subgroup of F_k at once.  It also compares the relative-threshold
margin with the exact tree value s_q(rho) - 1/q, where s_q(rho) is the smaller
root of d s/(1+q s^2) = 1/rho.
"""
import math


def worst(k, etas):
    q = 2 * k - 1
    d = q + 1
    rho_tree = 2 * math.sqrt(q) / d
    worst_ratio, worst_margin_ratio, used = 0.0, float("inf"), 0
    for eta in etas:
        rho = 1 - eta
        if rho < rho_tree:  # no quotient of F_k has rho_Q below the tree value
            continue
        used += 1
        M = 1 + 3 / eta ** 2
        s0 = 1 / q + eta / (4 * q)
        z = d * s0 / (1 + q * s0 ** 2)
        assert z * rho < 1, (k, eta)
        chi_bound = (1 - s0 ** 2) / (1 + q * s0 ** 2) / (1 - rho * z)
        worst_ratio = max(worst_ratio, chi_bound / M)
        # d s/(1+q s^2) = 1/rho  <=>  q s^2 - d rho s + 1 = 0
        disc = (d * rho) ** 2 - 4 * q
        s_exact = (d * rho - math.sqrt(max(disc, 0.0))) / (2 * q)
        margin = s_exact - 1 / q
        worst_margin_ratio = min(worst_margin_ratio, margin / (eta / (4 * q)))
    return worst_ratio, worst_margin_ratio, used


etas = [10 ** (-6 + 6 * i / 4000) for i in range(4001)]
for k in (2, 3, 4, 6, 10, 50):
    r, m, used = worst(k, etas)
    print(f"k={k:3d} ({used} eta values): max chi_bound/M = {r:.4f} "
          f"(<= 1 required); min exact margin/delta = {m:.3f} (>= 1 required)")
