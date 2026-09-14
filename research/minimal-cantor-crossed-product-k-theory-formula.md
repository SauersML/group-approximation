---
rg: 2
id: minimal-cantor-crossed-product-k-theory-formula
kind: claim
title: For a minimal Cantor system, K_n(LC(X,F_q)⋊Z) ≅ (K^0(X,T)⊗K_n(F_q)) ⊕ K_(n−1)(F_q) for n ≥ 1; over F_2, K_1 = Z, K_2 = 0, K_3 = K^0(X,T)/3
distinct_from:
  subshift-crossed-product-k0-is-coinvariant-group: that computes K_0 for any Cantor homeomorphism; this computes every K_n with n ≥ 1 for minimal systems, from the same fibration and Quillen's K_*(F_q)
artifacts:
  - research/artifacts/sk-open-4-dictionary-2026-09-13-part1.md
---

Let `(X,T)` be an infinite minimal Cantor system, `q` a prime power, `R_X = LC(X,F_q) ⋊_T Z` and
`K^0(X,T) = C(X,Z)/(1 − T_*)C(X,Z)`. For every `i ≥ 1`:
- `K_1(R_X) ≅ (K^0(X,T) ⊗ F_q^×) ⊕ Z`;
- `K_(2i)(R_X) ≅ Z/(q^i − 1)`;
- `K_(2i+1)(R_X) ≅ K^0(X,T) ⊗ Z/(q^(i+1) − 1)`.

Equivalently, `K_n(R_X) ≅ (K^0(X,T) ⊗ K_n(F_q)) ⊕ K_(n−1)(F_q)` for `n ≥ 1`. Together with
`subshift-crossed-product-k0-is-coinvariant-group` (`K_0(R_X) ≅ K^0(X,T)`), the algebraic K-theory of the ring is the
abstract dimension group tensored with `K_*(F_q)`, plus a copy of `K_(*−1)(F_q)`.

Over `F_2` (the note's ring): `K_1 ≅ Z`, `K_2 = 0`, `K_3 ≅ K^0(X,T)/3`, `K_4 ≅ Z/3`, `K_5 ≅ K^0(X,T)/7`, `K_6 ≅ Z/7`, and so on.

Blind spot: these groups depend only on the abstract group `K^0(X,T)`.
- All Sturmian subshifts give isomorphic K-groups, since `K^0 ≅ Z²`.
- Strong orbit equivalence needs the order and the unit (Giordano–Putnam–Skau).
- So K-theory of `R_X` cannot separate non-SOE Sturmians.

Proof in the `-proof` route and artifact part 1 §1. Unreviewed.
