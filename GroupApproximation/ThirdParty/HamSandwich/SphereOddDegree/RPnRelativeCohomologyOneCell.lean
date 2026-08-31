import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnAdditiveCohomology

/-!
# Relative cohomology of the one-cell pair `(RPⁿ, RPⁿ⁻¹)` over `F₂` (cellular step)

This file carries out the **one-cell relative cohomology step** needed to run the
additive induction for `H^k(RPⁿ; F₂)`. The classical statement is

```text
H^k(RPⁿ, RPⁿ⁻¹; F₂) ≅ F₂   if k = n,        H^k(RPⁿ, RPⁿ⁻¹; F₂) = 0   otherwise,
```

reflecting the single `n`-cell attached to `RPⁿ⁻¹` to form `RPⁿ`.

## Singular vs. cellular

The genuine *singular* relative cohomology of the pair is
`rpPairRelativeCohomology n k` (`RPnInclusionCohomology.lean`), defined as the
homology of the kernel of cochain restriction. Computing it from sphere
cohomology through the cofiber identification
`rpCofiberCohomologyIsoSphere` (`RPnQuotientSphereIso.lean`) requires two inputs
that pinned Mathlib does not provide and that are tracked as open blockers for
this branch:

* the good-pair / excision identification `H^k(RPⁿ⁺¹, RPⁿ; F₂) ≅ H̃^k(RPⁿ⁺¹/RPⁿ; F₂)`
  (equivalently `Epi (rpInclusionCochainMap n)`), and
* the unconditional sphere (co)homology computation, which in this project is
  itself only available conditionally (`SphereTopHomologyIso`,
  `SphereTopHomology.lean`).

Consequently this file proves the **cellular-local replacement** requested by the
prompt: the relative *cellular* cochain complex of the one-cell pair, which is
`F₂` in degree `n` and `0` elsewhere with zero differentials, together with its
cohomology computation and a packaged generator. This is the exact input the
additive induction consumes: it provides the new top cell `F₂` of `RPⁿ` over
`RPⁿ⁻¹`, matching the top cellular cohomology `rpCellularCohomology n n`.

All declarations are unconditional genuine homological algebra and reuse the
project's `cochainHomologyIsoOfZeroDiff` engine from `RPnAdditiveCohomology.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## The relative cellular cochain complex of the one-cell pair -/

/-- The `k`-th object of the relative cellular cochain complex of the pair
`(RPⁿ, RPⁿ⁻¹)`: a copy of `F₂` in the single degree `n` (the attached `n`-cell),
and the zero module in every other degree. -/
def rpRelativeCellularX (n k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  if k = n then ModuleCat.of (ZMod 2) (ZMod 2) else ModuleCat.of (ZMod 2) PUnit

/-- The **relative cellular cochain complex** of the one-cell pair `(RPⁿ, RPⁿ⁻¹)`
over `F₂`: `F₂` in degree `n`, zero elsewhere, with all differentials zero. A
genuine object of `CochainComplex (ModuleCat (ZMod 2)) ℕ`. -/
def rpRelativeCellularCochainComplex (n : ℕ) : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ where
  X := rpRelativeCellularX n
  d := fun _ _ => 0
  shape := by intro i j _; rfl
  d_comp_d' := by intro i j k _ _; simp

/-- The relative cellular cochain complex has zero differentials. -/
@[simp] theorem rpRelativeCellularCochainComplex_d (n i j : ℕ) :
    (rpRelativeCellularCochainComplex n).d i j = 0 := rfl

/-- In degree `n`, the relative cellular object is a copy of `F₂`. -/
def rpRelativeCellularX_iso_self (n : ℕ) :
    rpRelativeCellularX n n ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  eqToIso (by simp only [rpRelativeCellularX, if_true])

/-- Away from degree `n`, the relative cellular object is the zero module. -/
theorem rpRelativeCellularX_isZero_of_ne (n k : ℕ) (hk : k ≠ n) :
    IsZero (rpRelativeCellularX n k) := by
  simp only [rpRelativeCellularX, hk, if_false]
  exact ModuleCat.isZero_of_subsingleton _

/-! ## Relative cohomology of the one-cell pair (cellular) -/

/-- **The relative cohomology of the one-cell pair `(RPⁿ, RPⁿ⁻¹)` over `F₂`** (the
cellular replacement): the `k`-th homology of the relative cellular cochain
complex. -/
def rpCellularRelativeCochain_oneCell (n k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  (rpRelativeCellularCochainComplex n).homology k

/-- The relative cohomology in degree `k` is canonically the `k`-th relative
cellular object (zero differentials). -/
def rpCellularRelativeCochain_oneCell_iso_X (n k : ℕ) :
    rpCellularRelativeCochain_oneCell n k ≅ rpRelativeCellularX n k :=
  cochainHomologyIsoOfZeroDiff (rpRelativeCellularCochainComplex n)
    (rpRelativeCellularCochainComplex_d n) k

/-- **One-cell relative cohomology, top degree:** `H^n(RPⁿ, RPⁿ⁻¹; F₂) ≅ F₂`. -/
def rpRelativeCohomology_oneCell_iso (n : ℕ) :
    rpCellularRelativeCochain_oneCell n n ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  (rpCellularRelativeCochain_oneCell_iso_X n n) ≪≫ (rpRelativeCellularX_iso_self n)

/-- **One-cell relative cohomology, off the top degree:**
`H^k(RPⁿ, RPⁿ⁻¹; F₂) = 0` for `k ≠ n`. -/
theorem rpRelativeCohomology_oneCell_isZero (n k : ℕ) (hk : k ≠ n) :
    IsZero (rpCellularRelativeCochain_oneCell n k) :=
  (rpRelativeCellularX_isZero_of_ne n k hk).of_iso (rpCellularRelativeCochain_oneCell_iso_X n k)

/-- The relative cohomology of the one-cell pair is one-dimensional over `F₂` in
degree `n`. -/
theorem rpRelativeCohomology_oneCell_finrank (n : ℕ) :
    Module.finrank (ZMod 2) (rpCellularRelativeCochain_oneCell n n) = 1 := by
  rw [(rpRelativeCohomology_oneCell_iso n).toLinearEquiv.finrank_eq]
  simp

/-! ## Generator of the relative group -/

/-- **Generator of the relative one-cell group** `H^n(RPⁿ, RPⁿ⁻¹; F₂) ≅ F₂`: the
image of `1 ∈ F₂` under the inverse of the top-degree identification. -/
def rpRelativeCohomology_oneCell_generator (n : ℕ) :
    rpCellularRelativeCochain_oneCell n n :=
  (rpRelativeCohomology_oneCell_iso n).inv (1 : ZMod 2)

/-
The packaged generator is nonzero.
-/
theorem rpRelativeCohomology_oneCell_generator_ne_zero (n : ℕ) :
    rpRelativeCohomology_oneCell_generator n ≠ 0 := by
  by_contra h_zero
  convert congr_arg (fun x => (rpRelativeCohomology_oneCell_iso n).hom x) h_zero using 1
  simp +decide [rpRelativeCohomology_oneCell_generator]

/-- The relative one-cell group is nonzero in degree `n`. -/
theorem rpRelativeCohomology_oneCell_nonzero (n : ℕ) :
    ¬ IsZero (rpCellularRelativeCochain_oneCell n n) :=
  isZero_false_of_iso_F2 _ (rpRelativeCohomology_oneCell_iso n)

/-! ## Bridge to the absolute cellular top class (for the additive induction) -/

/-- **The one-cell relative group is the new top cell of `RPⁿ`.** In degree `n`,
the relative cohomology of the pair `(RPⁿ, RPⁿ⁻¹)` agrees with the top cellular
cohomology `H^n(RPⁿ; F₂)`: both are `F₂`. This is the inductive bridge the
additive computation consumes — the `n`-cell contributed by the pair is exactly
the top class of `RPⁿ`. -/
def rpRelativeCohomology_oneCell_iso_topCellular (n : ℕ) :
    rpCellularRelativeCochain_oneCell n n ≅ rpCellularCohomology n n :=
  (rpRelativeCohomology_oneCell_iso n) ≪≫
    (rpCellularCohomology_iso_in_range n n le_rfl).symm

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree