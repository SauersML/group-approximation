import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnAdditiveCohomology
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCohomologyRingModel
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnRelativeCohomologyOneCell

/-!
# Cellular cochain complex model for `RPⁿ` over `F₂`

This file packages the **cellular cochain model** of finite real projective space
over `F₂` under the canonical names requested by the model-bridge interface, and
records its structural properties:

```text
C^k_cell(RPⁿ; F₂) ≅ F₂   for 0 ≤ k ≤ n,        d = 0.
```

The concrete cochain complex `rpCellularCochainComplex n`
(`RPnAdditiveCohomology.lean`) is `F₂` in each degree `0 … n`, zero above, with
all differentials zero. This is the additive model underlying the ring
`F₂[α]/(αⁿ⁺¹)` (`RPnCohomologyRingModel.lean`).

What this file adds (all unconditional genuine homological algebra / linear
algebra; no projective-space input):

* `rpCellularCochainDifferential_eq_zero` — the cellular differential is the zero
  map over `ZMod 2` (canonical name).
* `rpCellularBasis n k` — the basis cochain in each degree `0 ≤ k ≤ n`, the image
  of `1 ∈ F₂`, together with `rpCellularBasis_ne_zero` and `rpCellularBasis_span`
  (it generates the one-dimensional cochain module).
* `rpCellularCohomologyGenerator n k` — the additive cohomology generator in each
  degree `0 ≤ k ≤ n`, with `rpCellularCohomologyGenerator_ne_zero` and
  `rpCellularCohomologyGenerator_span`.
* `rpModelPowerBasis n` — the explicit `F₂`-basis `(αᵏ)_{0 ≤ k ≤ n}` of the model
  ring `F₂[α]/(αⁿ⁺¹)`, the **model basis elements corresponding to the powers of
  `α`** (`rpModelPowerBasis_apply : rpModelPowerBasis n i = modelAlpha n ^ i`).

These give the explicit cellular/model generators on which a downstream prompt can
prove multiplicative compatibility.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Polynomial

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 1. Zero cellular differential (canonical name) -/

/-- **The cellular differential of `RPⁿ` is zero over `F₂`.** Canonical-named
alias of `rpCellularCochainComplex_d`: every differential of the cellular cochain
complex `rpCellularCochainComplex n` vanishes. -/
theorem rpCellularCochainDifferential_eq_zero (n i j : ℕ) :
    (rpCellularCochainComplex n).d i j = 0 :=
  rpCellularCochainComplex_d n i j

/-! ## 2. Basis cochain in each degree `0 ≤ k ≤ n` -/

/-- **Basis cochain in degree `k`** (`0 ≤ k ≤ n`): the image of `1 ∈ F₂` under the
identification `C^k_cell(RPⁿ; F₂) ≅ F₂`. This is the cellular cochain dual to the
`k`-cell of `RPⁿ`, the additive model of `αᵏ`. -/
def rpCellularBasis (n k : ℕ) (hk : k ≤ n) : (rpCellularCochainComplex n).X k :=
  (rpCellularX_iso_in_range n k hk).inv (1 : ZMod 2)

/-- The basis cochain in degree `k` is nonzero. -/
theorem rpCellularBasis_ne_zero (n k : ℕ) (hk : k ≤ n) :
    rpCellularBasis n k hk ≠ 0 := by
  by_contra h_zero
  convert congr_arg (fun x => (rpCellularX_iso_in_range n k hk).hom x) h_zero using 1
  simp [rpCellularBasis]

/-- The basis cochain in degree `k` generates the (one-dimensional) cochain
module `C^k_cell(RPⁿ; F₂)`. -/
theorem rpCellularBasis_span (n k : ℕ) (hk : k ≤ n) :
    Submodule.span (ZMod 2) {rpCellularBasis n k hk} = ⊤ := by
  set e : (rpCellularCochainComplex n).X k ≃ₗ[ZMod 2] ZMod 2 :=
    (rpCellularX_iso_in_range n k hk).toLinearEquiv with he
  have hb : rpCellularBasis n k hk = e.symm 1 := by
    show (rpCellularX_iso_in_range n k hk).inv (1 : ZMod 2) = e.symm 1
    rfl
  rw [hb, eq_top_iff]
  intro x _
  rw [Submodule.mem_span_singleton]
  exact ⟨e x, by simp [← e.injective.eq_iff]⟩

/-! ## 3. Cohomology generator in each degree `0 ≤ k ≤ n` -/

/-- **Cellular cohomology generator in degree `k`** (`0 ≤ k ≤ n`): the image of
`1 ∈ F₂` under `H^k_cell(RPⁿ; F₂) ≅ F₂`. Unconditional (model side); it is the
class represented by `rpCellularBasis n k`. -/
def rpCellularCohomologyGenerator (n k : ℕ) (hk : k ≤ n) :
    rpCellularCohomology n k :=
  (rpCellularCohomology_iso_in_range n k hk).inv (1 : ZMod 2)

/-- The cellular cohomology generator in degree `k` is nonzero. -/
theorem rpCellularCohomologyGenerator_ne_zero (n k : ℕ) (hk : k ≤ n) :
    rpCellularCohomologyGenerator n k hk ≠ 0 := by
  by_contra h_zero
  convert congr_arg (fun x => (rpCellularCohomology_iso_in_range n k hk).hom x) h_zero using 1
  simp [rpCellularCohomologyGenerator]

/-- The cellular cohomology generator in degree `k` generates the
(one-dimensional) group `H^k_cell(RPⁿ; F₂)`. -/
theorem rpCellularCohomologyGenerator_span (n k : ℕ) (hk : k ≤ n) :
    Submodule.span (ZMod 2) {rpCellularCohomologyGenerator n k hk} = ⊤ := by
  set e : rpCellularCohomology n k ≃ₗ[ZMod 2] ZMod 2 :=
    (rpCellularCohomology_iso_in_range n k hk).toLinearEquiv with he
  have hb : rpCellularCohomologyGenerator n k hk = e.symm 1 := by
    show (rpCellularCohomology_iso_in_range n k hk).inv (1 : ZMod 2) = e.symm 1
    rfl
  rw [hb, eq_top_iff]
  intro x _
  rw [Submodule.mem_span_singleton]
  exact ⟨e x, by simp [← e.injective.eq_iff]⟩

/-! ## 4. The model basis of powers of `α` -/

/-- **The power basis `(αᵏ)_{0 ≤ k ≤ n}` of the model ring `F₂[α]/(αⁿ⁺¹)`.** The
explicit `F₂`-basis of `RPnCohomologyRingModel n` given by the powers of the
generator `α = modelAlpha n`, indexed by `Fin (n+1)`. These are the model basis
elements that correspond, degree by degree, to the cellular generators. -/
def rpModelPowerBasis (n : ℕ) :
    Module.Basis (Fin (n + 1)) (ZMod 2) (RPnCohomologyRingModel n) :=
  (AdjoinRoot.powerBasis' (monic_X_pow (R := ZMod 2) (n + 1))).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis'_dim, natDegree_X_pow]))

/-- The `i`-th model basis element is the power `αⁱ`. -/
theorem rpModelPowerBasis_apply (n : ℕ) (i : Fin (n + 1)) :
    rpModelPowerBasis n i = modelAlpha n ^ (i : ℕ) := by
  show (AdjoinRoot.powerBasis' (monic_X_pow (R := ZMod 2) (n + 1))).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis'_dim, natDegree_X_pow])) i = _
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis'_gen]
  rfl

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
