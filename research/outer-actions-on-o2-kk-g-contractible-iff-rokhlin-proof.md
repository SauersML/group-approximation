---
rg: 2
id: outer-actions-on-o2-kk-g-contractible-iff-rokhlin-proof
kind: route
title: Rokhlin averaging puts O_2 in the fixed central sequences, Szabó's McDuff criterion absorbs id_O2, and Gabe--Szabó conjugacy identifies all contractible outer actions with the Rokhlin model
target: outer-actions-on-o2-kk-g-contractible-iff-rokhlin
requires: [izumi-rokhlin-approximately-representable-duality]
---

**Sources (read 2026-09-13 from ghostscript text extractions on MSI).**
* Hirshberg--Winter, *Rokhlin actions and self-absorbing C\*-algebras*,
  arXiv:math/0505356.  Definition 3.1: for `G` finite and `A` unital
  separable, `α` has the Rokhlin property if there is a partition of `1` into
  projections `{e_g} ⊆ A_∞ ∩ A'` with `ᾱ_g(e_h) = e_(gh)`.  Theorem 3.3: "Let
  A be a separable unital C\*-algebra, let G be a compact Hausdorff
  second-countable group, and let α : G → Aut(A) be an action satisfying the
  Rokhlin property. If B is a unital separable C\*-algebra which admits a
  central sequence of unital embeddings into A, then B admits a unital
  embedding into the fixed point subalgebra of A_∞ ∩ A′."
* Szabó, *Strongly self-absorbing C\*-dynamical systems*, arXiv:1509.08380.
  Corollary 3.8: for `G` second-countable locally compact, `A` separable, a
  cocycle action `(α, u)` and `D` strongly self-absorbing, (ii) "(A, α, u) is
  cocycle conjugate to (A ⊗ D, α ⊗ id_D, u ⊗ 1_D)" is equivalent to (iii)
  "There exists a unital, equivariant \*-homomorphism from D to the fixed
  point algebra F_(∞,α)(A)^(α̃)".
* Gabe--Szabó, arXiv:2205.04933: Theorem 3.13 (existence, with the unital
  version), Proposition 3.15 (isometrically shift-absorbing iff pointwise
  outer, for discrete `G` on Kirchberg algebras), and Corollary 6.4(ii):
  for compact `G` and isometrically shift-absorbing actions on unital
  Kirchberg algebras, "every invertible element x ∈ KK^G(α, β) with
  KK^G(ι_A) ⊗ x = KK^G(ι_B) lifts to a conjugacy".  Here `ι_A : C → A` is the
  unital inclusion.

**Standard inputs, not re-read.**
* (CC) Cocycle conjugate actions are KK^G-equivalent; exterior equivalence
  gives an equivariant Morita equivalence through the linking algebra.
* (TD) Takai duality: `(A ⋊ G) ⋊ Ĝ ≅ A ⊗ K(ℓ²G)` equivariantly, which is
  KK^G-equivalent to `(A, α)`.
* (KP) A unital Kirchberg algebra that is KK-contractible is `O_2`.  For outer
  `α` on `O_2`, `O_2 ⋊_α G` is a unital Kirchberg algebra (Kishimoto's
  simplicity and pure infiniteness of crossed products by outer actions, as
  cited in the proof of Barlak--Li II, Theorem 4.12).
* (SSA) If `A ≅ A ⊗ O_2`, then `O_2` admits a central sequence of unital
  embeddings into `A`: transport `x ↦ 1 ⊗ ⋯ ⊗ 1 ⊗ x` into the `n`-th factor of
  `A ⊗ O_2^(⊗∞) ≅ A`.  `O_2 ⊗ M_(k^∞) ≅ O_2`.

**Item 1.**  By (SSA) and Hirshberg--Winter Theorem 3.3, there is a unital
`O_2 → (A_∞ ∩ A')^(ᾱ)`.  For finite `G` and unital `A`, `F_(∞,α)(A)` is
`A_∞ ∩ A'`.  Szabó Corollary 3.8, (iii) ⟹ (ii), gives `α ≃_cc α ⊗ id_(O_2)`.
By (CC), `(A, α) ≃_(KK^G) (A, α) ⊗ τO_2`.  Now `τ : KK → KK^G` is a functor
and `id_(O_2) = 0` in `KK(O_2, O_2)`, so `id_(τO_2) = 0`.  The exterior product
is bilinear, so `id_((A,α) ⊗ τO_2) = id_(A,α) ⊗ id_(τO_2) = 0`.

**Item 2.**
* *Model.*  `μ_G` on `M_(|G|^∞) = ⊗_n B(ℓ²G)` is Rokhlin: take `e_g` to be the
  rank-one projection onto `δ_g` in the `n`-th factor, and let `n → ∞`.  So
  `id ⊗ μ_G` on `O_2 ⊗ M_(|G|^∞) ≅ O_2` is Rokhlin, with the same `e_g ⊗ 1`.
  It is contractible by item 1.
* *Rokhlin implies pointwise outer.*  If `α_g = Ad(u)` with `u ∈ A` and
  `g ≠ 1`, then `e_1 ∈ A'` gives `e_g = ᾱ_g(e_1) = u e_1 u* = e_1`, which
  contradicts `e_g e_1 = 0` and `e_1 ≠ 0`.
* *Contractible and outer implies conjugate to the model.*  Both `α` and the
  model are isometrically shift-absorbing by Proposition 3.15.  Both objects
  are zero, so `x = 0 ∈ KK^G(α, id ⊗ μ_G)` is invertible, and
  `KK^G(ι) ∈ KK^G(C, zero object) = 0` on both sides.  Corollary 6.4(ii) lifts
  `x` to a conjugacy.
* *Conjugate to the model implies Rokhlin.*  The Rokhlin property is invariant
  under conjugacy.
* *Rokhlin implies contractible.*  This is item 1, since `O_2 ≅ O_2 ⊗ O_2`.

**Item 3.**  Let `D` be nuclear with `Res D ≃ 0`, and let
`H = ℓ²G ⊗ ℓ²N` with `λ ⊗ 1`.
1. `(D ⊗ K(H), δ ⊗ Ad(λ ⊗ 1))` is equivariantly Morita equivalent to `D`.
2. Let `s_1, s_2` be Cuntz isometries on `ℓ²N`.  The isometries `1 ⊗ 1 ⊗ s_i` in
   `M(D ⊗ K(H))` are fixed by the action.  Put
   `E = D ⊗ K(H) + C*(s_1, s_2)`.  This is a separable unital nuclear
   `G`-algebra, with a split extension
   `0 → D ⊗ K(H) → E → τO_2 → 0`, split by `C*(s_1, s_2) ⊆ E`.
3. By split exactness, `E ≃_(KK^G) D ⊕ τO_2 ≃ D`.
4. Theorem 3.13, unital version, embeds `E` unitally into an isometrically
   shift-absorbing action `β` on a unital Kirchberg algebra `B`, inducing a
   KK^G-equivalence.  By Proposition 3.15, `β` is pointwise outer.
   `B ≃_KK Res D ≃ 0`, so `B ≅ O_2` by (KP).  Descent gives
   `B ⋊_β G ≃_KK D ⋊ G`.
5. Hence detection for `D` is detection for `(O_2, β)`.  By item 2 that is the
   Rokhlin property of `β`.  Conversely, every outer `α` on `O_2` with
   contractible crossed product is such a `D`.

**Item 4.**  `C = O_2 ⋊_α G` is a unital Kirchberg algebra with `C ≃_KK 0`, so
`C ≅ O_2` by (KP).  If `α` is approximately representable, then `α̂` has the
Rokhlin property, by the duality in
`izumi-rokhlin-approximately-representable-duality`, item 2.  Item 1 applied
to `(C, α̂)` gives `(C, α̂) ≃_(KK^Ĝ) 0`.  By (TD), the dual crossed product
`C ⋊ Ĝ` is KK^G-equivalent to `(O_2, α)`, so `α ≃_(KK^G) 0`.  Item 2 then
makes `α` Rokhlin.  For outer strongly approximately inner actions, item 3 of
that node gives approximate representability when `p` is prime.
