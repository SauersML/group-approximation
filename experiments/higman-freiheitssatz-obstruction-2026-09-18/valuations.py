"""2-adic bookkeeping for the b-twist S_e = b^-1 [a,c]^2 b in Gamma(3, 2^e).

t = 3^-1 mod 2^e, lam = 3^t mod 2^e.  Then S_e = (a^-1 c^-lam a c^3)^2 and
e_c(S_e) = 2(3 - lam) mod 2^e.  Claims checked here for e = 3..80:
  (1) lam = 3 mod 8                       (so S_e maps to [a,c^3]^2 in Abar_8);
  (2) v_2(3 - lam) = 3, so v_2(e_c(S_e)) = 4 once e >= 5 (e_c = 0 mod 16 always);
  (3) v_2(3^(16 w) - 1) = 6 for odd w, so d^(1 - 3^(e_c)) generates <d^64>;
  (4) the whole b-orbit: v_2(3^k - 3^(k t)) = 3 + v_2(k) for k != 0, so no twist b^-k R b^k has
      e_c of valuation below 4.
"""


def v2(x):
    x = abs(x)
    if x == 0:
        return float("inf")
    k = 0
    while x % 2 == 0:
        x //= 2
        k += 1
    return k


ok = True
for e in range(3, 81):
    m = 2 ** e
    t = pow(3, -1, m)
    lam = pow(3, t, m)
    ec = (2 * (3 - lam)) % m
    c1 = lam % 8 == 3
    # for e = 3 the residue lam is exactly 3 (3 - lam = 0); from e = 4 on v_2(3 - lam) = 3
    c2 = (e == 3 and lam == 3 or v2(3 - lam) == 3) and (e < 5 or v2(ec) == 4) and ec % 16 == 0
    orbit = all(v2((pow(3, k, m) - pow(3, (k * t) % m, m)) % m) >= min(e, 3 + v2(k))
                for k in range(1, min(m, 4096)))
    orbit_exact = all(v2((pow(3, k, m) - pow(3, (k * t) % m, m)) % m) == 3 + v2(k)
                      for k in range(1, min(m, 4096)) if 3 + v2(k) < e)
    ok &= c1 and c2 and orbit and orbit_exact
    if e <= 12 or e % 10 == 0:
        print(f"e={e:2d} t={t % 64:2d}(mod 64) lam mod 64={lam % 64:2d} lam mod 8={lam % 8} "
              f"v2(3-lam)={v2(3 - lam)} e_c(S_e) mod 2^e has v2={v2(ec) if ec else 'inf'} "
              f"orbit bound ok={orbit and orbit_exact}")
for w in range(1, 2000, 2):
    ok &= v2(3 ** (16 * w) - 1) == 6
print("v2(3^(16w)-1) = 6 for all odd w < 2000:", all(v2(3 ** (16 * w) - 1) == 6 for w in range(1, 200, 2)))
print("ALL CHECKS PASS:", ok)
