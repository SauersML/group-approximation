# Density test for the diagonal R = T^a S^b on Siefken's parameter space of the
# Kari--Culik minimal subsystem KC, restricted to the invariant family
#   F = {(alpha, iota(c*alpha))}  (row phases on the real line of the solenoid).
# Model (Siefken, arXiv:1410.1572, Theorem A): That(alpha,t) = (alpha, t+alpha),
# Shat(alpha,t) = fhat(alpha,t) = (lam*alpha, lam*t), lam = 2 on [1/3,1), 1/3 on [1,2].
# Hence R^n(alpha0, iota(c alpha0)) = (alpha_n, iota((c + n a) alpha_n)),
# alpha_n = f^{bn}(alpha0).  We project the fibre to R/6^k Z (proj_k) and report
# the fraction of a G x G grid on (log6-angle of alpha_n, proj_k) that is visited.
# Coverage near 1 for every k is what minimality of R on the closure of F predicts.
import math

LOG6 = math.log(6)


def f(x):
    return 2 * x if x < 1 else x / 3


def coverage(a, b, c, alpha0, N, k, G):
    M = 6 ** k
    seen = set()
    al = alpha0
    for n in range(1, N + 1):
        for _ in range(b):
            al = f(al)
        eta = (math.log(al) / LOG6 + math.log(3) / LOG6) % 1.0
        val = ((c + n * a) * al) % M
        seen.add((int(eta * G), int(val / M * G)))
    return len(seen) / (G * G)


if __name__ == "__main__":
    alpha0 = math.sqrt(2)
    for (a, b) in [(1, 1), (1, 2), (2, 1), (3, 1)]:
        row = []
        for k in [0, 1, 2]:
            row.append(round(coverage(a, b, 0.3183, alpha0, 400000, k, 40), 4))
        print("a=%d b=%d coverage k=0,1,2:" % (a, b), row)
