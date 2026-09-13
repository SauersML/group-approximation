---
rg: 2
id: sl3-level-q-elementary-group-contains-e3-of-q-squared-proof
kind: route
title: Write level-q-squared opposite conjugates as commutators of level-q elementary products
target: sl3-level-q-elementary-group-contains-e3-of-q-squared
requires:
  - sl3-relative-elementary-generated-by-opposite-conjugates
artifacts:
  - research/artifacts/zp-sl3z-elementary-congruence-finite-index-2026-09-13.md
---

1. **Commutator identity.** For `a, b ∈ q`, `c ∈ A`, `i != j` and third
   index `l`, the relation `e_ij(ab) = [e_il(a), e_lj(b)]` together with the
   conjugation formulas gives

   `z_ij(ab, c) = e_ji(c) e_ij(ab) e_ji(-c) = [e_jl(ca) e_il(a), e_li(-bc) e_lj(b)]`.

   All four entries lie in `q`, so `z_ij(ab, c) ∈ F(q)`.
2. **Additivity.** `t ↦ z_ij(t, c)` is a homomorphism from `(A, +)`, and every
   element of `q^2` is a sum of products `ab`. So `z_ij(t, c) ∈ F(q)` for all
   `t ∈ q^2`.
3. **Conclusion.** By `sl3-relative-elementary-generated-by-opposite-conjugates`
   with `J = q^2`, these elements generate `E_3(A, q^2)`. Hence
   `E_3(A, q^2) <= F(q)`.

This is Lemma B and Theorem C of the artifact.
