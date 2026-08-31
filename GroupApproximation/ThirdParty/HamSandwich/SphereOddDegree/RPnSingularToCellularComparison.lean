import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCellularCochainStructure
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCohomologyRingBridge

/-!
# Singular-to-cellular cochain comparison for `RPⁿ` (additive)

This file constructs the comparison between the **actual singular cohomology** of
`RPⁿ` and the **cellular / model cohomology**, in the additive form usable by the
model-bridge structure `RPnCohomologyToModelHom n`:

```text
H^k_sing(RPⁿ; F₂) ≅ H^k_cell(RPⁿ; F₂)        (singularToCellularRPnCohomologyIso)
```

and, transporting one step further into the algebraic model ring
`RPnCohomologyRingModel n = F₂[α]/(αⁿ⁺¹)`, an explicit linear comparison

```text
H^k_sing(RPⁿ; F₂) ≃ₗ[F₂]  F₂ · αᵏ ⊆ F₂[α]/(αⁿ⁺¹)     (0 ≤ k ≤ n)
```

carrying the canonical degree-`k` cohomology generator to the model power `αᵏ`.
This is the additive "transport to the model and back": being a *linear
equivalence*, every actual cohomology class is sent to the model and recovered on
the nose (`rpCohomologyModelEquiv_symm_apply_apply`).

All declarations are conditional on the single honest input
`RPnCellularCochainStructure n` (the Mathlib-absent cellular-approximation
identification of the singular cochain complex of `RPⁿ` with the cellular model;
see `Axioms_And_Placeholders.md`), through which the genuine singular cohomology
`rpCohomology n k` is identified with the cellular model.

## Scope: additive only

The comparison delivered here is **additive** (`F₂`-linear). Multiplicativity —
i.e. that the per-degree maps assemble into a *ring* homomorphism with
`map_one'` and `map_cup'` (the cup product going to the model product) — is **not**
proved here and is left for the next prompt. The degree-indexed family
`rpCohomologyToModelToFun` provides exactly the additive `toFun` field of
`RPnCohomologyToModelHom n`; supplying the `map_one'`, `map_cup'`, `alpha`, and
`alpha_spec` fields is the remaining multiplicative work.
-/

noncomputable section

open CategoryTheory AlgebraicTopology
open Polynomial

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

variable {n : ℕ}

/-! ## 1. Singular cohomology ≅ cellular cohomology -/

/-- **Singular-to-cellular cohomology comparison.** Given the cellular-cochain
input `c`, the genuine singular cohomology of `RPⁿ` agrees, in every degree, with
the cellular model cohomology:
`H^k_sing(RPⁿ; F₂) ≅ H^k_cell(RPⁿ; F₂)`. This is the core additive bridge. -/
def singularToCellularRPnCohomologyIso (c : RPnCellularCochainStructure n) (k : ℕ) :
    rpCohomology n k ≅ rpCellularCohomology n k :=
  c.cohomologyIso k

/-- Alias of `singularToCellularRPnCohomologyIso` under the candidate name. -/
def rpSingularToCellularCohomologyIso (c : RPnCellularCochainStructure n) (k : ℕ) :
    rpCohomology n k ≅ rpCellularCohomology n k :=
  singularToCellularRPnCohomologyIso c k

/-! ## 2. Additive comparison with the model ring -/

/-- **Additive transport to the model and back.** For `0 ≤ k ≤ n`, the actual
singular cohomology `H^k(RPⁿ; F₂)` is linearly isomorphic to the degree-`k`
model line `F₂ · αᵏ ⊆ F₂[α]/(αⁿ⁺¹)`. Being a linear equivalence, it transports
each class to the model and recovers it exactly. -/
def rpCohomologyModelEquiv (c : RPnCellularCochainStructure n) (k : ℕ) (hk : k ≤ n) :
    rpCohomology n k ≃ₗ[ZMod 2] (ZMod 2 ∙ (modelAlpha n ^ k)) :=
  (rpCohomology_additive_iso_zmod2 c k hk).toLinearEquiv.trans
    (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (RPnCohomologyRingModel n)
      (modelAlpha n ^ k) (modelAlpha_pow_ne_zero n k hk))

/-- Round-trip: transporting a class to the model line and back returns it. -/
@[simp] theorem rpCohomologyModelEquiv_symm_apply_apply
    (c : RPnCellularCochainStructure n) (k : ℕ) (hk : k ≤ n) (x : rpCohomology n k) :
    (rpCohomologyModelEquiv c k hk).symm (rpCohomologyModelEquiv c k hk x) = x :=
  (rpCohomologyModelEquiv c k hk).symm_apply_apply x

/-- Round-trip: transporting a model-line element back and forth returns it. -/
@[simp] theorem rpCohomologyModelEquiv_apply_symm_apply
    (c : RPnCellularCochainStructure n) (k : ℕ) (hk : k ≤ n)
    (y : (ZMod 2 ∙ (modelAlpha n ^ k))) :
    rpCohomologyModelEquiv c k hk ((rpCohomologyModelEquiv c k hk).symm y) = y :=
  (rpCohomologyModelEquiv c k hk).apply_symm_apply y

/-- **The additive comparison map into the model ring.** For `0 ≤ k ≤ n`, the
`F₂`-linear map `H^k(RPⁿ; F₂) → F₂[α]/(αⁿ⁺¹)` obtained by transporting to the
model line and including it into the model ring. -/
def rpCohomology_additive_toModel (c : RPnCellularCochainStructure n) (k : ℕ) (hk : k ≤ n) :
    rpCohomology n k →ₗ[ZMod 2] RPnCohomologyRingModel n :=
  (Submodule.subtype _).comp (rpCohomologyModelEquiv c k hk).toLinearMap

/-- The additive comparison map into the model ring is injective: distinct
cohomology classes have distinct model images. -/
theorem rpCohomology_additive_toModel_injective (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : k ≤ n) :
    Function.Injective (rpCohomology_additive_toModel c k hk) := by
  intro a b hab
  apply (rpCohomologyModelEquiv c k hk).injective
  apply Subtype.coe_injective
  simpa only [rpCohomology_additive_toModel, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.coe_subtype] using hab

/-! ## 3. The canonical generator and its model image -/

/-- The canonical degree-`k` cohomology generator (`0 ≤ k ≤ n`): the preimage of
`1 ∈ F₂` under the additive isomorphism `H^k(RPⁿ; F₂) ≅ F₂`. -/
def rpCohomologyGenerator (c : RPnCellularCochainStructure n) (k : ℕ) (hk : k ≤ n) :
    rpCohomology n k :=
  (rpCohomology_additive_iso_zmod2 c k hk).toLinearEquiv.symm 1

/-- The canonical generator is nonzero. -/
theorem rpCohomologyGenerator_ne_zero (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : k ≤ n) : rpCohomologyGenerator c k hk ≠ 0 := by
  rw [rpCohomologyGenerator, Ne, LinearEquiv.map_eq_zero_iff]
  exact one_ne_zero

/-- **The model image of the canonical generator is `αᵏ`.** This is the precise
degree-by-degree correspondence between the actual cohomology generator and the
model power basis element. -/
theorem rpCohomology_additive_toModel_generator (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : k ≤ n) :
    rpCohomology_additive_toModel c k hk (rpCohomologyGenerator c k hk)
      = modelAlpha n ^ k := by
  rw [rpCohomology_additive_toModel, rpCohomologyGenerator]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, rpCohomologyModelEquiv,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Submodule.coe_subtype]
  rw [LinearEquiv.toSpanNonzeroSingleton_one]

/-- **The model image of the canonical generator is nonzero** (`αᵏ ≠ 0`). Together
with injectivity, this confirms classes transport faithfully to the model. -/
theorem rpCohomology_model_generator_nonzero (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : k ≤ n) :
    rpCohomology_additive_toModel c k hk (rpCohomologyGenerator c k hk) ≠ 0 := by
  rw [rpCohomology_additive_toModel_generator]
  exact modelAlpha_pow_ne_zero n k hk

/-! ## 4. The additive `toFun` field of `RPnCohomologyToModelHom n` -/

/-- **The additive degree-indexed comparison family** `toFun` of the model bridge
`RPnCohomologyToModelHom n`. In range (`k ≤ n`) it is the additive comparison
`rpCohomology_additive_toModel`; above the dimension (where `H^k = 0`) it is the
zero map. Supplying the remaining `map_one'`, `map_cup'`, `alpha`, `alpha_spec`
fields (multiplicativity) is the work left for the next prompt. -/
def rpCohomologyToModelToFun (c : RPnCellularCochainStructure n) :
    (k : ℕ) →
      (cohomologyZMod2 (TopCat.of (RP n)) k →ₗ[ZMod 2] RPnCohomologyRingModel n) :=
  fun k => if hk : k ≤ n then rpCohomology_additive_toModel c k hk else 0

/-- In range, the additive `toFun` family is the additive comparison map. -/
theorem rpCohomologyToModelToFun_of_le (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : k ≤ n) :
    rpCohomologyToModelToFun c k = rpCohomology_additive_toModel c k hk := by
  rw [rpCohomologyToModelToFun, dif_pos hk]

/-- Above the dimension, the additive `toFun` family is the zero map. -/
theorem rpCohomologyToModelToFun_of_gt (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : n < k) :
    rpCohomologyToModelToFun c k = 0 := by
  rw [rpCohomologyToModelToFun, dif_neg (by omega)]

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
