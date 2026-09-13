import json, math, sys
sys.path.insert(0, "/scratch.global/sauer354/thompson-f-cogrowth")
from fractions import Fraction
import cogrowth_exact as ce
d = json.load(open("/scratch.global/sauer354/thompson-f-cogrowth/hhr_certify.json"))
ours = [1, 4, 28, 232, 2092, 19884, 196096, 1988452, 20612364, 217561120, 2331456068,
        25311956784, 277937245744, 3082543843552, 34493827011868, 389093033592912]
c2 = ours + d["hhr_c2_16_to_24"]
M = [Fraction(c, 16 ** j) for j, c in enumerate(c2)]   # moments of mu_2 (P^2 at delta_e)
# measure nu = y dmu_2(y): moments N_j = M_{j+1}, j = 0..23; supp nu subset supp mu_2 in [0,1]
Nmom = M[1:]
def cert(mom):
    N = len(mom) - 1
    k = (N + 1) // 2
    p_prev, p, norms = [Fraction(0)], [Fraction(1)], []
    for j in range(k):
        nj = ce.inner(p, p, mom); norms.append(nj)
        assert nj > 0
        alpha = ce.inner(ce.poly_mul_x(p), p, mom) / nj
        beta = nj / norms[j - 1] if j > 0 else Fraction(0)
        p_next = ce.poly_add(ce.poly_add(ce.poly_mul_x(p), p, 1, -alpha), p_prev, 1, -beta)
        p_prev, p = p, p_next
    assert ce.poly_eval(p, Fraction(1)) > 0
    grid = [Fraction(i, 4096) for i in range(4096, -1, -1)]
    lo = next(t for t in grid if ce.poly_eval(p, t) < 0); hi = lo + Fraction(1, 4096)
    for _ in range(60):
        mid = (lo + hi) / 2
        if ce.poly_eval(p, mid) < 0: lo = mid
        else: hi = mid
    theta = Fraction(math.floor(lo * 10 ** 9), 10 ** 9)
    neg = ce.poly_eval(p, theta) < 0
    r = Fraction(math.isqrt(math.floor(theta * 10 ** 12)), 10 ** 6)
    return {"k": k, "theta": "%d/%d" % (theta.numerator, theta.denominator), "p_k_at_theta_negative": neg,
            "rho_lower_bound": "%d/%d" % (r.numerator, r.denominator), "rho_lower_bound_float": float(r),
            "norm_T2_lower_bound_float": 4 * float(r), "r_squared_le_theta": r * r <= theta}
print(json.dumps({"even_measure_k12": d["cert_N24"], "odd_measure_y_dmu2_k12": cert(Nmom)}, indent=1))
