#!/usr/bin/env python3
"""Check the moment lemma for alternating words in U_3(p) and U_4(p) (lane hl-surface-girth-general).

For every word x^{a_1} y^{b_1} ... x^{a_m} y^{b_m} with all exponents in F_p^* (m = 3 for U_3, m = 4 for U_4 with
x designated) compare:
  law      the normal-form collection law (beta, gamma, mu, nu all 0 mod p);
  moment   sum b = 0, sum a = 0, sum_r a_r H_r^d = 0 for 1 <= d <= m-2, H_r = b_1 + ... + b_{r-1};
  classify m = 3: a = lam (H2-H3, H3-H1, H1-H2) with distinct heights;
           m = 4: distinct heights with a_r = lam / prod_{s != r} (H_r - H_s), or H1 = H3 != H2 = H4 with
                  a = (a1, a2, -a1, -a2);
and the counts (p-1)^2 (p-2) and (p-1)^2 ((p-2)(p-3) + (p-1)).
"""
from itertools import product


def law(m, a, b, p):
    beta = gamma = mu = nu = 0
    for s in range(m):
        gamma += a[s]
        e = b[s]; nu += gamma * e * (e - 1) // 2 + e * mu; mu += e * gamma; beta += e
    ok = beta % p == 0 and gamma % p == 0 and mu % p == 0
    return ok if m == 3 else ok and nu % p == 0


def heights(m, b, p):
    H = [0]
    for s in range(m - 1): H.append((H[-1] + b[s]) % p)
    return H


def moment(m, a, b, p):
    if sum(a) % p or sum(b) % p: return False
    H = heights(m, b, p)
    return all(sum(a[r] * pow(H[r], d, p) for r in range(m)) % p == 0 for d in range(1, m - 1))


def classify(m, a, b, p):
    if sum(b) % p: return False
    H = heights(m, b, p)
    if len(set(H)) == m:
        w = []
        for r in range(m):
            den = 1
            for s in range(m):
                if s != r: den = den * (H[r] - H[s]) % p
            w.append(pow(den, p - 2, p))
        lam = a[0] * pow(w[0], p - 2, p) % p
        return all(a[r] % p == lam * w[r] % p for r in range(m))
    if m == 4 and H[0] == H[2] and H[1] == H[3]:
        return (a[0] + a[2]) % p == 0 and (a[1] + a[3]) % p == 0
    return False


ok_all = True
for m, primes in ((3, (3, 5, 7, 11, 13)), (4, (5, 7, 11, 13))):
    for p in primes:
        halves = [t + ((-sum(t)) % p,) for t in product(range(1, p), repeat=m - 1) if (-sum(t)) % p]
        n_law = n_mom = n_cls = agree = total = 0
        for a in halves:
            for b in halves:
                x, y, z = law(m, a, b, p), moment(m, a, b, p), classify(m, a, b, p)
                total += 1; n_law += x; n_mom += y; n_cls += z; agree += (x == y == z)
        formula = (p - 1) ** 2 * (p - 2) if m == 3 else (p - 1) ** 2 * ((p - 2) * (p - 3) + (p - 1))
        good = agree == total and n_law == formula
        ok_all = ok_all and good
        print("m", m, "p", p, "words with zero exponent sums", total, "law", n_law, "moment", n_mom, "classify", n_cls,
              "formula", formula, "all agree", agree == total, "PASS" if good else "FAIL", flush=True)
print("moment lemma checks:", "ALL PASS" if ok_all else "SOME FAIL")
