---
rg: 2
id: radu-lattice-one-sided-pairs-need-radius-five
kind: claim
title: A one-sided inverse pair over Radu's lattice needs supports of total radius at least five
distinct_from:
  radu-lattice-one-sided-pairs-need-residual-coincidences: that forces two defect points into one coset of the finite residual, so total radius at least four; this squares the defect idempotent on those coincidences, excludes radius four, and excludes radius five under a finite hypothesis.
  radu-lattice-defect-idempotents-avoid-finite-subgroups: that keeps the defect idempotent out of finite-subgroup algebras; this plays the idempotent law against the support of the defect.
artifacts:
  - research/artifacts/radu-lattice-radius-four-linear-pairs-2026-09-12.md
---

**ESTABLISHED** by `radu-lattice-one-sided-pairs-need-radius-five-proof`. Verification requested from
w4-vf-linear-b.

Let `Gamma_R`, `Gamma_0`, `B_r` and `delta = xz` be as in
`radu-lattice-one-sided-pairs-need-residual-coincidences`. Let `S_r` be the sphere and `K` any field.
Let `A, B in M_n(K[Gamma_R])` with `B A = I_n`, put `D = I_n - A B`, and suppose
`S_A ⊆ u B_r w` and `S_B ⊆ w^(-1) B_s u^(-1)` for some `u, w`.

**Theorem.**
1. **Radius four.** If `r + s <= 4`, then `A B = I_n`. So `(B_2,B_2)`, `(B_1,B_3)` and `(B_3,B_1)`
   carry no pair at any size. Only `Gamma_0 ∩ B_8 ⊆ {1, delta^(+-4)}` (Remark 3.6) is used, not
   `delta^4 in Gamma_0`.
2. **Product-free criterion.** Let `C_k` be the set of points of `B_k` that share a coset of `Gamma_0`
   with another point of `B_k`. If `r + s = k` and `C_k C_k ∩ C_k = ∅`, then `A B = I_n`.
3. **Radius five, conditionally.** Suppose `Gamma_0 ∩ S_10 ⊆ {y delta^4 y, y delta^(-4) y}` (H10).
   Then `C_5` is product-free, so `r + s = 5` forces `A B = I_n`.
4. **Radius six.** `C_6` contains `delta` and `delta^2`, so item 2 does not apply at `r + s = 6`.

**Mechanism.** `D` is idempotent and vanishes modulo `Gamma_0`. At radius four, `D = E (delta^2 - delta^(-2))`
with `E in M_n(K)`, and `D^2 = E^2 (delta^4 - 2 + delta^(-4))` has disjoint support, so `E = 0`.
The same holds over any commutative ring.
