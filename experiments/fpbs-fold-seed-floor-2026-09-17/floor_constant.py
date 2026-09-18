"""First-moment sparsity constant for random permutation actions of F_2.

For |I| = m = alpha*n and k = (1+eta)*m spanned slots, the first moment is
  C(n,m) * C(2m,k) * (m/n)^k,
whose exponential rate per n is
  E(alpha,eta) = H(alpha) + 2 alpha h((1+eta)/2) + (1+eta) alpha ln(alpha)
(H, h: natural-log binary entropies).  When E < 0 the probability that some
m-set spans >= k slots decays exponentially.  The seed floor is then
  c0 = (1-eta) * alpha / 2.
We also evaluate the exact log first moment at finite n as a sanity check.
"""
from math import log, lgamma


def H(x):
    return 0.0 if x in (0.0, 1.0) else -x * log(x) - (1 - x) * log(1 - x)


def rate(alpha, eta):
    return H(alpha) + 2 * alpha * H((1 + eta) / 2) + (1 + eta) * alpha * log(alpha)


def lbinom(N, K):
    return lgamma(N + 1) - lgamma(K + 1) - lgamma(N - K + 1)


def exact_log_bound(n, alpha, eta):
    m = int(alpha * n) + 1
    k = int((1 + eta) * m) + 1
    if k > 2 * m:
        return float("-inf")
    return lbinom(n, m) + lbinom(2 * m, k) + k * log(m / n)


def largest_alpha(eta):
    lo, hi = 1e-12, 0.5
    if rate(hi, eta) < 0:
        return hi
    for _ in range(200):
        mid = (lo + hi) / 2
        if rate(mid, eta) < 0:
            lo = mid
        else:
            hi = mid
    return lo


best = (0.0, None, None)
for i in range(1, 400):
    eta = i / 400
    a = largest_alpha(eta)
    c0 = (1 - eta) * a / 2
    if c0 > best[0]:
        best = (c0, a, eta)
c0, a, eta = best
print("optimal eta=%.4f alpha=%.6f  c0=(1-eta)alpha/2=%.6f" % (eta, a, c0))
print("rate at 0.99*alpha: %.3e" % rate(0.99 * a, eta))
for n in (10**4, 10**5, 10**6):
    print("n=%d exact log first moment at 0.99 alpha: %.2f"
          % (n, exact_log_bound(n, 0.99 * a, eta)))
for (al, et) in ((0.02, 0.5), (0.01, 0.5), (0.001, 0.5)):
    print("alpha=%.3f eta=%.2f rate=%.5f floor=%.6f"
          % (al, et, rate(al, et), (1 - et) * al / 2))
