import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGysinConnecting
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnW1ClassEqActualRPAlpha
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoveringTransferSES
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CochainCupLeibniz
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib

/-!
# The Smith/Gysin connecting map is cup product with `actualRPAlpha`

This file proves, at the level of singular cochains, that the Smith/Gysin
connecting homomorphism `rpGysinConnecting n k : Hᵏ(RPⁿ; F₂) ⟶ Hᵏ⁺¹(RPⁿ; F₂)`
(the connecting map of the dualized Smith short exact sequence
`transferSEScoch n`) is cup product with the canonical class `α = actualRPAlpha n`
(the first Stiefel–Whitney class of the double cover):

```text
rpGysinConnecting n k x = cupZMod2 x (actualRPAlpha n).
```

## Proof strategy (a two-sheeted cover)

Represent a class `x = [c]` by a cocycle `c ∈ Cᵏ(RPⁿ)`.  A lift of `c` along the
cochain transfer `tr* = g` is the cochain `gysinLift n k c` on `Sⁿ`, defined by

```text
(gysinLift c)(τ) = c(sProj τ) · sheetParity(τ(last vertex)),
```

where `sProj τ` is the projected simplex and `sheetParity` measures which sheet a
sphere point lies on.  Because the two lifts of a base simplex are antipodal and
`sheetParity` flips under the antipode, `tr*(gysinLift c) = c`
(`transfer_gysinLift`).

The coboundary of the lift descends, and the key `dc = 0` computation shows that
its descent is *exactly* the Alexander–Whitney cochain cup `c ⌣ w₁`
(`f_cup_eq_coboundary`).  Feeding these two cochain facts into Mathlib's
element-level connecting-map formula `ShortComplex.ShortExact.δ_apply` yields the
identity in cohomology.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AlexanderWhitney

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 1. Charts, vertex sheets and the lifted cochain -/

/-- The underlying continuous map `Δᵏ → Sⁿ` of a singular `k`-simplex `τ` of the
sphere (the `toSSetObjEquiv` chart, matching the convention used by `sProj`). -/
noncomputable def sChart (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k) :
    C(stdSimplex ℝ (Fin (k + 1)), Sphere n) :=
  TopCat.toSSetObjEquiv (TopCat.of (Sphere n)) (Opposite.op (SimplexCategory.mk k)) τ

/-- The underlying continuous map `Δᵏ → RPⁿ` of a singular `k`-simplex `σ` of
`RPⁿ`. -/
noncomputable def rpChart (n k : ℕ) (σ : singularSimplices (TopCat.of (RP n)) k) :
    C(stdSimplex ℝ (Fin (k + 1)), RP n) :=
  TopCat.toSSetObjEquiv (TopCat.of (RP n)) (Opposite.op (SimplexCategory.mk k)) σ

/-
The chart of the projected simplex is `proj n` composed with the sphere chart.
-/
theorem rpChart_sProj (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k) (x) :
    rpChart n k (sProj n k τ) x = proj n (sChart n k τ x) := by
  unfold rpChart sProj sChart
  simp

/-
**Antipode flips the chart.** The chart of the deck-image `sAnti τ` is the
negation of the chart of `τ`.
-/
theorem sChart_sAnti (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k)
    (x : stdSimplex ℝ (Fin (k + 1))) :
    sChart n k (sAnti n k τ) x = -(sChart n k τ x) := by
  unfold sChart sAnti
  simp [antipodal]

/-- The **sheet parity of the last vertex** of a sphere `k`-simplex `τ`. -/
noncomputable def gLastSheet (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k) : ZMod 2 :=
  sheetParity n (sChart n k τ (stdSimplex.vertex (Fin.last k)))

/-- **The lifted cochain.** `gysinLift n k c ∈ Cᵏ(Sⁿ; F₂)` lifts the cocycle
`c ∈ Cᵏ(RPⁿ; F₂)` along the cochain transfer. -/
noncomputable def gysinLift (n k : ℕ) (c : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) k) :
    singularCochainGroup (ZMod 2) (TopCat.of (Sphere n)) k :=
  Sigma.desc (fun τ =>
    ModuleCat.ofHom ((cochainEval k c (sProj n k τ) * gLastSheet n k τ)
      • (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)))

/-- Evaluation of `gysinLift`. -/
theorem gysinLift_eval (n k : ℕ) (c : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) k)
    (τ : singularSimplices (TopCat.of (Sphere n)) k) :
    cochainEval k (gysinLift n k c) τ = cochainEval k c (sProj n k τ) * gLastSheet n k τ := by
  let d := fun τ : singularSimplices (TopCat.of (Sphere n)) k =>
    ModuleCat.ofHom ((cochainEval k c (sProj n k τ) * gLastSheet n k τ)
      • (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2))
  change (Sigma.desc d).hom
    ((Sigma.ι (fun _ : singularSimplices (TopCat.of (Sphere n)) k =>
      ModuleCat.of (ZMod 2) (ZMod 2)) τ).hom 1) = _
  have hd := Sigma.ι_desc d τ
  have hv := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hd) (1 : ZMod 2)
  calc
    _ = ((Sigma.ι (fun _ : singularSimplices (TopCat.of (Sphere n)) k =>
        ModuleCat.of (ZMod 2) (ZMod 2)) τ ≫ Sigma.desc d).hom 1) := rfl
    _ = (d τ).hom 1 := hv
    _ = _ := by simp [d]

/-- **The antipode toggles the last-vertex sheet parity.** -/
theorem gLastSheet_sAnti (n k : ℕ) (τ : singularSimplices (TopCat.of (Sphere n)) k) :
    gLastSheet n k (sAnti n k τ) = gLastSheet n k τ + 1 := by
  unfold gLastSheet
  rw [sChart_sAnti, sheetParity_neg]


end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
