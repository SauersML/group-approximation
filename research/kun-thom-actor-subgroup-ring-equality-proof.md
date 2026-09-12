---
rg: 2
id: kun-thom-actor-subgroup-ring-equality-proof
kind: route
title: Realize p by an elementary matrix, torus primes inside SL_r(F_q), and small primes by cyclotomic companion matrices
target: kun-thom-actor-finite-subgroup-ring-equals-z-inverted-p
requires:
  - kun-thom-actor-finite-subgroup-ring-has-finitely-many-primes
artifacts:
  - research/artifacts/bc-kun-thom-trace-test-2026-09-12.md
---

The containment `Lambda^G ⊆ Z[1/P]` is the required claim. For the reverse, it suffices to exhibit
an element of order `l` in `G` for every prime `l` in `P(q,r,d)`.

1. **`l = p`.** The elementary matrix `e_12(1) ∈ EL_r(R)` has order `p`.
2. **`l | q^k - 1`, `1 <= k <= r`.** `F_q ⊆ R`, and `SL_r(F_q) = E_r(F_q) ⊆ EL_r(R)`. Also
   `|SL_r(F_q)| = q^(r(r-1)/2) prod_(j=2..r) (q^j - 1)`.
   - If `k >= 2`, `l` divides a factor of that order.
   - If `k = 1`, `l | q - 1 | q^2 - 1`.
   Cauchy's theorem gives an element of order `l`.
3. **Odd prime `l <= d + 1`.** The companion matrix of `Phi_l` lies in `GL_(l-1)(Z)`. It has
   determinant `(-1)^(l-1) Phi_l(0) = 1` and order `l`. Pad it with `I_(d-l+1)`.
4. **`l = 2`.** `diag(-1, -1, 1, ..., 1) ∈ SL_d(Z)`, since `d >= 3`.

So `Z[1/P] ⊆ Lambda^G`, and equality holds. QED
