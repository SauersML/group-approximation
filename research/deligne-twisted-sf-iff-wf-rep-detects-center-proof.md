---
rg: 2
id: deligne-twisted-sf-iff-wf-rep-detects-center-proof
kind: route
title: Antipode and scalar restriction remove j and F, the graded theorem gives items 1-4, and cutting by central idempotents gives item 5
target: deligne-twisted-sf-iff-wf-rep-detects-center
requires:
  - lef-graded-simple-base-sf-iff-rank-condition
  - finitely-generated-linear-groups-are-residually-finite
  - residually-finite-groups-are-lef
  - deligne-triple-cover-finite-residual-is-center
artifacts:
  - research/artifacts/deligne-twisted-sf-rank-condition-dichotomy-2026-09-16.md
---

Artifact Section 3, Theorem 3.1.

## Why sufficient

1. **LEF.** `Sp_4(Z)` is a finitely generated subgroup of `GL_4(Q)`, so it is residually finite
   (`finitely-generated-linear-groups-are-residually-finite`). It is therefore LEF
   (`residually-finite-groups-are-lef`: a finite quotient injective on `E ∪ E·E` preserves the partial
   multiplication table of `E`). Each `A_j(F)` is a twisted
   group algebra, strongly graded with simple base `F`, so `lef-graded-simple-base-sf-iff-rank-condition`
   applies over any field.
2. **Independence of `j`.** The antipode `g -> g^(-1)` of `F[E_3]` maps `z - w^j` to
   `-w^j z^(-1)(z - w^(-j))`, so `A_j(F)^op ≅ A_(3-j)(F)`. Stable finiteness passes to opposites via
   transposition.
3. **Independence of `F`.** `A_j(F_0) ⊂ A_j(F)` is unital. `A_j(F)` is a free right `A_j(F_0)`-module on an
   `F_0`-basis of the central field `F`, so left multiplication embeds `A_j(F)` unitally in
   `M_d(A_j(F_0))`.
4. **Items 1–4.** By steps 2–3, items 1 and 2 are both equivalent to `A_1(F_0)` not being stably finite.
   The graded theorem turns this into items 3 and 4.
5. **Item 5 implies item 1.** If `A_1(F_0)` were stably finite, then `E_3 -> A_1(F_0)^x` would send `z` to
   `w != 1`, with `A_1(F_0)` nonzero, weakly finite and of characteristic `p`.
6. **Item 1 implies item 5.** Let `rho : E_3 -> R^x` with `R != 0` weakly finite, `p·1 = 0` and
   `rho(z) != 1`.
   - `R' = R ⊗_(F_p) F_0` embeds unitally in `M_2(R)` or equals `R`, so it is weakly finite and contains
     `R`.
   - Let `S` be the image of `F_0[E_3] -> R'`, which is weakly finite. The elements
     `e_k = (1/3) Σ_i w^(-ki) rho(z)^i` are central orthogonal idempotents of `S` with `rho(z) e_k = w^k e_k`.
   - `rho(z) - 1 = (w - 1)e_1 + (w^2 - 1)e_2 != 0`, so some `e_j != 0` with `j in {1, 2}`.
   - The corner `S e_j` is weakly finite: `XY = e_j I` gives `(X + (1-e_j)I)(Y + (1-e_j)I) = I` in `M_n(S)`.
   - `x -> x e_j` is a unital homomorphism `F_0[E_3] -> S e_j` killing `z - w^j`. So `A_j(F_0)` has a nonzero
     weakly finite image and is stably finite by the graded theorem, and item 1 fails by steps 2–4.
7. **`N_p` is `1` or `<z>`.** For `g ∉ <z>`, `deligne-triple-cover-finite-residual-is-center` gives a finite
   quotient `Q` in which `g` survives. The faithful regular representation `Q -> GL_(|Q|)(F_p)` lands in a
   weakly finite ring of characteristic `p`, so `N_p <= <z> ≅ C_3`, and `N_p` is normal.
