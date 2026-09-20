#!/usr/bin/env python3
"""Density comparison between the DKKMS per-tuple B-subspace law P0 and the
uniform law U on Gr(F_2^(3k), l-1).

rho(Q) = dP0/dU(Q) = sum_V P(V) 1[Q <= X_V] |Gr(3k,l-1)| / |Gr(3k-2m,l-1)|,
where V smooths each of the k blocks independently with probability beta and
keeps one uniform variable of a smoothed block (m = number of smoothed blocks).

Checks:
 (a) exact law of N_i(Q) = #{v : pi_i(Q) <= <e_v>} for a uniform linear map
     F_2^(l-1) -> F_2^3, and its first two moments;
 (b) Gaussian-binomial sandwich 4^(m r) <= [n,r]/[n-2m,r] <= K0 4^(m r),
     K0 = prod_j (1 - 2^-(n-2m-j))^-1, hence phi <= rho <= K0 phi with
     phi(Q) = prod_i ((1-beta) + (beta/3) 4^(l-1) N_i(Q));
 (c) exact enumeration at tiny (k,l): E_U rho = 1, rho >= phi pointwise, and
     E_U rho^2 against the closed form (1 + beta^2 (4^(l-1)(1+2^(2-l))/3 - 1))^k;
 (d) the seed-signal invariant S = k beta^2 4^(l-1)/3 at beta = ln ln k / k on
     the q = 1 window: at k_A(l), k_T(l) = 4^(l-1)/12, k_0(l) (least k with
     SD* <= 1e-5), and at the certified lower bound k >= 2^(4 l^2 + 12).
Prints ALL PASS on success.
"""
import itertools
import math
from fractions import Fraction

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def gauss_binom(n, r):
    num, den = 1, 1
    for j in range(r):
        num *= (2 ** (n - j) - 1)
        den *= (2 ** (j + 1) - 1)
    return num // den


# (a) law of N for a uniform 3 x (l-1) matrix over F_2 (rows r_1, r_2, r_3)
print("(a) law of N_i")
for l in range(2, 7):
    r = l - 1
    counts = {}
    total = 0
    for rows in itertools.product(range(2 ** r), repeat=3):
        n_i = sum(1 for v in range(3)
                  if all(rows[u] == 0 for u in range(3) if u != v))
        counts[n_i] = counts.get(n_i, 0) + 1
        total += 1
    p3 = Fraction(counts.get(3, 0), total)
    p1 = Fraction(counts.get(1, 0), total)
    en = sum(Fraction(c * n, total) for n, c in counts.items())
    en2 = sum(Fraction(c * n * n, total) for n, c in counts.items())
    check(p3 == Fraction(1, 8 ** r), f"P(N=3) l={l}")
    check(p1 == Fraction(3 * (2 ** r - 1), 8 ** r), f"P(N=1) l={l}")
    check(set(counts) <= {0, 1, 3}, f"support l={l}")
    check(en == Fraction(3, 4 ** r), f"E N l={l}")
    check(en2 == Fraction(3, 4 ** r) + Fraction(6, 8 ** r), f"E N^2 l={l}")
    b = Fraction(4 ** r, 3)  # b / beta
    # E[(1-beta) + beta b N] = 1 exactly, for every beta
    check((b * en) == 1, f"mean factor one l={l}")
    print(f"  l={l}: P(N=3)={p3}, P(N=1)={p1}, E N={en}, E N^2={en2}")

# (b) Gaussian-binomial sandwich
print("(b) Gaussian-binomial sandwich")
for k in range(2, 9):
    n = 3 * k
    for r in range(1, min(6, k)):
        for m in range(0, k + 1):
            ratio = Fraction(gauss_binom(n, r), gauss_binom(n - 2 * m, r))
            lo = Fraction(4 ** (m * r))
            k0 = Fraction(1)
            for j in range(r):
                k0 /= (1 - Fraction(1, 2 ** (n - 2 * m - j)))
            check(lo <= ratio <= k0 * lo, f"sandwich k={k} r={r} m={m}")
print("  sandwich holds on k=2..8, r<min(6,k), all m")


# (c) exact enumeration at tiny parameters (3k - 2k >= l - 1, so every X_V
#     contains (l-1)-spaces; DKKMS has k >= l + 1)
def rank_f2(vecs):
    vecs = list(vecs)
    rk = 0
    bits = max((v.bit_length() for v in vecs), default=0)
    for bit in range(bits):
        piv = None
        for i in range(rk, len(vecs)):
            if vecs[i] >> bit & 1:
                piv = i
                break
        if piv is None:
            continue
        vecs[rk], vecs[piv] = vecs[piv], vecs[rk]
        for i in range(len(vecs)):
            if i != rk and vecs[i] >> bit & 1:
                vecs[i] ^= vecs[rk]
        rk += 1
    return rk


def block_rows(basis, i):
    # rows r_1, r_2, r_3 of pi_i M, each an (l-1)-bit integer
    rows = []
    for c in range(3):
        coord = 3 * i + c
        rows.append(sum(((v >> coord) & 1) << j for j, v in enumerate(basis)))
    return rows


print("(c) exact enumeration")
for (k, l, beta) in [(2, 2, 0.3), (2, 3, 0.3), (2, 3, 0.1), (3, 2, 0.2),
                     (3, 3, 0.15), (2, 3, 0.5)]:
    r = l - 1
    n = 3 * k
    # X_V of dimension n - 2m < r contains no r-space; its ratio is never used
    ratios = [gauss_binom(n, r) / gauss_binom(n - 2 * m, r)
              if gauss_binom(n - 2 * m, r) > 0 else 0.0
              for m in range(k + 1)]
    b = beta * 4 ** r / 3
    s1 = s2 = f2 = 0.0
    cnt = 0
    ok = True
    for basis in itertools.permutations(range(1, 2 ** n), r):
        if rank_f2(basis) < r:
            continue
        cnt += 1
        nis = []
        for i in range(k):
            rows = block_rows(basis, i)
            nis.append([v for v in range(3)
                        if all(rows[u] == 0 for u in range(3) if u != v)])
        # rho: sum over smoothing patterns (T, v)
        rho = 0.0
        for pattern in itertools.product(range(4), repeat=k):
            # 3 = kept block, 0..2 = smoothed keeping variable v
            m = sum(1 for p in pattern if p < 3)
            w = 1.0
            inside = True
            for i, p in enumerate(pattern):
                if p == 3:
                    w *= (1 - beta)
                else:
                    w *= beta / 3
                    if p not in nis[i]:
                        inside = False
                        break
            if inside:
                rho += w * ratios[m]
        phi = 1.0
        for i in range(k):
            phi *= (1 - beta) + b * len(nis[i])
        if rho < phi * (1 - 1e-12):
            ok = False
        s1 += rho
        s2 += rho * rho
        f2 += phi * phi
    e1, e2, ef2 = s1 / cnt, s2 / cnt, f2 / cnt
    closed = (1 + beta ** 2 * (4 ** r * (1 + 2 ** (2 - l)) / 3 - 1)) ** k
    S = k * beta ** 2 * 4 ** r / 3
    check(abs(e1 - 1) < 1e-9, f"E rho = 1 at k={k} l={l}")
    check(ok, f"rho >= phi at k={k} l={l}")
    check(e2 >= ef2 * (1 - 1e-12), f"E rho^2 >= E phi^2 at k={k} l={l}")
    print(f"  k={k} l={l} beta={beta}: E rho={e1:.12f}  E rho^2={e2:.5f}"
          f"  E phi^2={ef2:.5f}  closed(iid)={closed:.5f}  S={S:.4f}")


# (d) the invariant S on the q = 1 window
print("(d) seed signal S = k beta^2 4^(l-1)/3 at beta = ln ln k / k")


def S_of(l, k):
    beta = math.log(math.log(k)) / k
    return k * beta ** 2 * 4 ** (l - 1) / 3


def SD_of(l, k):
    beta = math.log(math.log(k)) / k
    return beta * math.sqrt(k) * 2 ** (l + 3) + 3 * 2 ** (l - k)


def k0(l):
    hi = 16  # ln ln k > 0 from here on, and SD* decreases in k
    while SD_of(l, hi) > 1e-5:
        hi *= 2
    lo = hi // 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if SD_of(l, mid) <= 1e-5:
            hi = mid
        else:
            lo = mid
    return hi


for l in [20, 25, 30, 40, 60]:
    kA = math.exp(l) * (2 * l * math.log(2) + math.log(4 * 192 ** 2))
    kT = 4 ** (l - 1) / 12
    kz = k0(l)
    # k where S = 1, located by bisection on log k
    lo, hi = math.log(kA), math.log(kz)
    for _ in range(200):
        mid = (lo + hi) / 2
        if S_of(l, math.exp(mid)) > 1:
            lo = mid
        else:
            hi = mid
    kS1 = math.exp(hi)
    kcert_log2 = 4 * l * l + 12
    # S at the certified lower bound, computed in logs
    lnk = kcert_log2 * math.log(2)
    S_cert_log10 = (2 * math.log(lnk) + (l - 1) * math.log(4) - math.log(3)
                    - lnk) / math.log(10)
    SA, ST, S0 = S_of(l, kA), S_of(l, kT), S_of(l, kz)
    check(SA > ST > 1 > S0, f"S ordering l={l}")
    check(kA < kT < kS1 < kz, f"k ordering l={l}")
    print(f"  l={l}: log2 kA={math.log2(kA):.1f} S={SA:.3g} | "
          f"log2 kT={math.log2(kT):.1f} S={ST:.3g} | "
          f"log2 k(S=1)={math.log2(kS1):.1f} | "
          f"log2 k0={math.log2(kz):.1f} S={S0:.3g} | "
          f"certified log2 k>={kcert_log2}, log10 S<={S_cert_log10:.0f}")
    # identity S = SD1^2 / 768 with SD1 = beta sqrt(k) 2^(l+3)
    beta = math.log(math.log(kz)) / kz
    sd1 = beta * math.sqrt(kz) * 2 ** (l + 3)
    check(abs(S0 - sd1 ** 2 / 768) < 1e-9 * max(1, S0), f"S = SD1^2/768 l={l}")

print("ALL PASS" if not FAIL else f"{len(FAIL)} FAILURES")
