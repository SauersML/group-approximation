---
rg: 2
id: product-two-graph-kp-elementary-simple-kazhdan-not-mf
kind: claim
title: For m, n >= 2, EL_N over L_(F_q)(1,m) ⊗ L_(F_q)(1,n) (the product rank-2 graph algebra) mod centre is an infinite fg simple Kazhdan group with no nontrivial MF quotient
distinct_from:
  simple-dedekind-infinite-ring-elementary-full-mf-radical: that is the no-MF-quotient conclusion for every simple not directly finite ring; this adds simplicity modulo centre and property (T) for the explicit tensor product of two Leavitt algebras, through the product Cuntz groupoid.
  kp-algebra-steinberg-simple-iff-aperiodic-cofinal: that imports the general Kumjian–Pask simplicity and Steinberg picture; this proves the one-vertex product case directly and adds the group consequences.
artifacts:
  - research/artifacts/un-boundary-families-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed; proof in `product-two-graph-kp-elementary-simple-kazhdan-not-mf-proof`).**

**Setting.** Let `m, n >= 2`, let `q` be a prime power, let `N >= 3`, and put
`R_(m,n) = L_(F_q)(1, m) ⊗_(F_q) L_(F_q)(1, n)`.

**Statement.** `R_(m,n) ≅ A_(F_q)(𝒢_m × 𝒢_n)`, where `𝒢_m` and `𝒢_n` are Cuntz groupoids.
`EL_N(R_(m,n))/Z` is an infinite finitely generated simple group with property (T), and every homomorphism from it to
an MF group is trivial.

Recalled, not imported: `R_(m,n)` is the Kumjian–Pask algebra of the one-vertex product 2-graph `Λ_m × Λ_n`, which is
cofinal and aperiodic.

**Review (un-verify-3, 2026-09-13): PASS.** Checked: `Λ_m × Λ_n` groupoid minimal and effective (Cuntz groupoids effective since `αz = βz` with `|α| ≠ |β|` has one solution); `A(𝒢_m) ⊗ A(𝒢_n) ≅ A(𝒢_m × 𝒢_n)` (multiplicative, surjective on products of compact opens, injective by pointwise linear independence); `(t_2⊗1)(1 − s_1t_1⊗1)(s_2⊗1) = 1`; then the interface theorem. `research/artifacts/un-review3-2026-09-13-part4.md` §6.
