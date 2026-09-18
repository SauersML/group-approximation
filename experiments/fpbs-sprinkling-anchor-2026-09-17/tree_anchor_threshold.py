"""Tree-anchor one-edge sprinkling thresholds for Cay(F_k x Z, standard) = T_{2k} x Z.

Anchor: bond percolation at p on the a_i-edges only (disjoint copies of T_{2k}),
t-edges closed. Sprinkling the t-edges at rate r = p (fresh generator, p_e = 0).
Lemma (fpbs-one-edge-sprinkling-l2-lipschitz): ||T_p(T_{2k} x Z)|| <= L/(1 - 2 p L)
whenever 2 p L < 1, where L >= ||T_p(T_{2k})||. Schur test with the ground spherical
function Xi(n) = (1 + n (q-1)/(q+1)) q^(-n/2), q = 2k-1, gives
||T_p(T_{2k})|| <= Lambda_q(p) = 1 + ((q+1)/q) sum_{n>=1} (1 + n c) x^n,  x = sqrt(q) p.
"""
import math


def Lam(q, p):
    x = math.sqrt(q) * p
    assert x < 1
    c = (q - 1) / (q + 1)
    s0 = x / (1 - x)
    s1 = x / (1 - x) ** 2
    return 1 + (q + 1) / q * (s0 + c * s1)


def check_xi(q, N=40):
    # A Xi = 2 sqrt(q) Xi on the (q+1)-regular tree (radial recursion)
    c = (q - 1) / (q + 1)
    xi = [(1 + n * c) * q ** (-n / 2) for n in range(N + 2)]
    lam = 2 * math.sqrt(q)
    err = abs((q + 1) * xi[1] - lam * xi[0])
    for n in range(1, N + 1):
        err = max(err, abs(xi[n - 1] + q * xi[n + 1] - lam * xi[n]))
    return err


def check_lambda_series(q, p, N=2000):
    # brute force: sum_n |S_n| p^n Xi(n)
    c = (q - 1) / (q + 1)
    tot = 1.0
    for n in range(1, N):
        tot += (q + 1) / q * (math.sqrt(q) * p) ** n * (1 + n * c)
    return abs(tot - Lam(q, p))


def threshold(q):
    lo, hi = 0.0, 0.999999 / math.sqrt(q)
    for _ in range(200):
        mid = (lo + hi) / 2
        if 2 * mid * Lam(q, mid) < 1:
            lo = mid
        else:
            hi = mid
    return lo


print("k deg  p*(tree anchor)  walk-count 1/||A||  1/(deg-1)  pc(T_2k)=1/(2k-1)  2pL at pc(T_2k)  unconditional")
for k in range(2, 9):
    q = 2 * k - 1
    deg = 2 * k + 2
    ps = threshold(q)
    wc = 1 / (2 * math.sqrt(q) + 2)
    pt = 1 / q
    val = 2 * pt * Lam(q, pt)
    print(f"{k} {deg:3d}  {ps:.6f}         {wc:.6f}            {1/(deg-1):.6f}   {pt:.6f}           {val:.4f}           {val < 1}")
    assert check_xi(q) < 1e-12
    assert check_lambda_series(q, ps) < 1e-9

p = 0.2
phiZ = (1 - p) / (1 + p)  # amenable anchor: ||T|| = chi = (1+p)/(1-p)
print("\nF_2 x Z anchors at p = 1/5 <= pc (transfer needs p*||A_added|| < 1/||T_anchor||):")
print(" empty anchor : p||A_S|| =", p * (2 * math.sqrt(3) + 2), "vs 1")
print(" anchor {t}   : p*2sqrt3 =", p * 2 * math.sqrt(3), "vs phi_Z =", phiZ)
print(" anchor {a}   : p*4      =", p * 4, "vs phi_Z =", phiZ)
chi_lb = 1 + 4 * p + 4 * p ** 2 + 4 * (2 * p ** 2 - p ** 4)
print(" anchor {a,t} : p*2      =", p * 2, "vs phi_Z2 <= 1/chi_lb =", 1 / chi_lb, "(inconclusive)")
print(" anchor {a,b} : p*2      =", p * 2, "vs 1/Lambda_3(p) =", 1 / Lam(3, p), "(succeeds at p=1/5)")
print(" tree-anchor threshold for F_2 x Z: p* =", threshold(3))
