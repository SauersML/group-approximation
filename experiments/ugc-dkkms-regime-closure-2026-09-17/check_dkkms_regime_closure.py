#!/usr/bin/env python3
"""Check: DKKMS-certified parameter points lie in the Theorem S regime.

Claim: dkkms-certified-parameters-lie-in-the-selector-kill-regime.

DKKMS (ECCC TR16-198) proof of Lemma 5.3 uses, at its parameter point
(delta, l, k, q), with beta = log log k / k and alpha(l) = delta1 2^(-l^2-2)
(Lemma 3.7 proof, delta1 <= 1 the agreement parameter it is applied at):

  (P1) Pr_Q[Q not smooth] <= sqrt(beta sqrt k) <= alpha(l)/2
       (Lemma 4.10 plus the step Pr[E1 and not E2] <= delta/2 * alpha/2;
        DKKMS even write the stronger sqrt(beta) k^(1/4) 2^(l+5) << alpha/2);
  (P2) eps_k = exp(-k/exp(q l)) < delta alpha(l)/4
       (the final contradiction with Lemma 5.4 goes through (16), whose
        lower bound is delta alpha/4 times a conditional win probability <= 1).

Theorem S (near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp)
needs
  (R) l >= 3 and SD* = beta sqrt(k) 2^(l+3) + 3 2^(l-k) <= 1e-5;
  (A) 2^(l-1-2k) <= 1/16 and eps_k <= p0^2/4, p0 = 2^(-l)/192.

All four sets are upward closed in k (for k >= 16), so it suffices to test
the least k with (P1) and (P2), taking delta = delta1 = 1 (the most
permissive case; smaller delta only raises k).  Everything is in log space,
since k is about 2^(4 l^2).  Both natural and base-2 readings of log log are
checked.  Part (b) shows that the q = 1 window of Corollary S3 (points with
(A) but not (R)) violates (P1) everywhere, so it is not a DKKMS point.
"""
import math

LN2 = math.log(2.0)


def lnlnk(x, base2):
    """log log k given x = ln k."""
    if base2:
        return math.log(x / LN2) / LN2  # log2(log2 k)
    return math.log(x)


def ln_beta_sqrtk(x, base2):
    """ln(beta sqrt k) = ln(loglog k) - x/2."""
    return math.log(lnlnk(x, base2)) - x / 2.0


def least_lnk(pred, lo=math.log(16.0)):
    """Least x = ln k >= lo with pred(x) (pred upward closed), by bisection."""
    hi = lo
    while not pred(hi):
        hi = 2 * hi + 1
    for _ in range(200):
        mid = (lo + hi) / 2
        if pred(mid):
            hi = mid
        else:
            lo = mid
    return hi


def ln_alpha(l):
    return -(l * l + 2) * LN2


def p1(x, l, base2):
    # sqrt(beta sqrt k) <= alpha/2  <=>  ln(beta sqrt k) <= 2 ln alpha - 2 ln 2
    return ln_beta_sqrtk(x, base2) <= 2 * ln_alpha(l) - 2 * LN2


def p2(x, l, q):
    # exp(-k/e^{ql}) < alpha/4  <=>  k > e^{ql} * (-(ln alpha - 2 ln 2))
    return x > q * l + math.log(-(ln_alpha(l) - 2 * LN2))


def ln_sd_star_parts(x, l, base2):
    a = ln_beta_sqrtk(x, base2) + (l + 3) * LN2
    k = math.exp(min(x, 700.0))
    b = math.log(3.0) + (l - k) * LN2  # 3 2^(l-k)
    return a, b


def cond_R(x, l, base2):
    a, b = ln_sd_star_parts(x, l, base2)
    m = max(a, b)
    ln_sd = m + math.log(math.exp(a - m) + math.exp(b - m))
    return l >= 3 and ln_sd <= math.log(1e-5)


def cond_A(x, l, q):
    k = math.exp(min(x, 700.0))
    ok1 = (l - 1 - 2 * k) * LN2 <= -4 * LN2
    ln_p0sq4 = 2 * (-l * LN2 - math.log(192.0)) - math.log(4.0)
    # ln eps_k = -k/e^{ql} = -exp(x - q l)
    ok2 = -math.exp(min(x - q * l, 700.0)) <= ln_p0sq4
    return ok1 and ok2


def main():
    bad = []
    worst = None
    for base2 in (False, True):
        for q in range(1, 13):
            for l in range(3, 201):
                x = least_lnk(lambda t: p1(t, l, base2) and p2(t, l, q))
                r, a = cond_R(x, l, base2), cond_A(x, l, q)
                if not (r and a):
                    bad.append((base2, q, l, r, a))
                sd = ln_sd_star_parts(x, l, base2)[0] / LN2
                if worst is None or sd > worst[0]:
                    worst = (sd, base2, q, l)
    print("(a) least DKKMS-certified k per (q, l), q = 1..12, l = 3..200, both loglog bases")
    print("    points failing (R) or (A):", [(b, q, l, r, a) for (b, q, l, r, a) in bad])
    print("    all failures have l <= 4:", all(l <= 4 for (_, _, l, _, _) in bad))
    print("    largest log2(beta sqrt k 2^(l+3)) at a certified point: %.2f (q=%d, l=%d, base2=%s)"
          % (worst[0], worst[2], worst[3], worst[1]))
    # (b) the q = 1 window of Corollary S3: k_A(l) <= k < k_0(l)
    print("(b) q = 1 window of Corollary S3 against (P1)")
    viol = 0
    total = 0
    for l in range(3, 201):
        ln_p0sq4 = 2 * (-l * LN2 - math.log(192.0)) - math.log(4.0)
        xA = l + math.log(-ln_p0sq4)  # least ln k with (A) at q = 1
        x0 = least_lnk(lambda t: cond_R(t, l, False))
        if xA < x0:
            total += 1
            # every k in the window has k < k_0, test P1 at its top end (P1 upward closed)
            if not p1(x0, l, False):
                viol += 1
    print("    window nonempty at %d values of l; (P1) fails on the whole window at %d of them"
          % (total, viol))
    ok = all(l <= 4 for (_, _, l, _, _) in bad) and viol == total
    print("RESULT:", "PASS" if ok else "FAIL")


if __name__ == "__main__":
    main()
