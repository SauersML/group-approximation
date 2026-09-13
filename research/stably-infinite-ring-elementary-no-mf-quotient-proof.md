---
rg: 2
id: stably-infinite-ring-elementary-no-mf-quotient-proof
kind: route
title: Apply the rank-two criterion to M_n(R) and use EL_2(M_n(R)) = EL_2n(R)
target: stably-infinite-ring-elementary-groups-have-no-mf-quotient
requires:
  - full-idempotent-ring-has-properly-infinite-unit
  - full-defect-ring-non-mf-at-rank-two
artifacts:
  - research/artifacts/un-paradox-stable-infiniteness-2026-09-13.md
---

## Why sufficient

1. **Lemma 1 of the artifact.** `2n[1] <= n[1]` in `V(R)` holds iff `S = M_n(R)` contains `v_0, v_1,
   w_0, w_1` with `w_i v_j = delta_ij 1`. The summand inclusions and projections of
   `R^n (+) R^n (+) Z ~= R^n` are elements of `End_R(R^n) = M_n(R)`.
2. **Properly infinite unit.** By `full-idempotent-ring-has-properly-infinite-unit` (2 ⇒ 1), `S` has
   `ts = 1` with `S(1-st)S = S`.
3. **Rank two.** By `full-defect-ring-non-mf-at-rank-two` applied to the countable unital ring `S`,
   every homomorphism from `EL_2(S)` to an MF group is trivial.
4. **Block identity (Lemma 2).** For `m >= 2`, `EL_m(M_n(R)) = EL_(mn)(R)`. A block elementary matrix
   is a product of commuting elementary matrices with entries in its block. An intra-block elementary
   matrix is the commutator `[e_((I,a),(J',a))(r), e_((J',a),(I,b))(1)]` for any block `J' != I`. So
   the rank `N = 2n` is done.
5. **All ranks `N > 2n`.** Here `N >= 3`. A homomorphism to an MF group is trivial on the copy
   `diag(EL_(2n)(R), I)`, hence on every `e_12(r)`. Signed permutation matrices spread `e_12(r)` to
   every `e_ij(+-r)`, so it is trivial.
6. **Corollary.** `M_n(R)` is simple and not directly finite, so `e = 1 - st != 0` is full. That gives
   condition 1 of `full-idempotent-ring-has-properly-infinite-unit` in `M_n(R)`, hence (PI), hence
   `2n[1] <= n[1]`.
