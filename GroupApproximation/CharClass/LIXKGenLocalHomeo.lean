import GroupApproximation.CharClass.LIXKGenDeriv
import GroupApproximation.CharClass.EulerLocalChart
import GroupApproximation.CharClass.RelativeLocalModel
import GroupApproximation.CharClass.MayerVietorisElement
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import GroupApproximation.Meta.AxiomGuard

/-!
# The local homeomorphism at the zero, and its punctured pair, at rank `n`

Lane `lix-oddside-n` (predecessor report `sp-oddside-n.md` §0.3, file E).

The inverse function theorem applied to `CharClass/LIXKGenDeriv.lean`'s strict derivative gives
`eulerLocalHomeo n`, the local homeomorphism of the section's trivial block at its zero, read in
the chart of `S^{2n+1} × S¹` at `(−e₀, 0)`.  `cc-thom`'s `openPartialHomeomorphChartPair` turns
it into a homeomorphism of punctured pairs, and `relCohomologyCongrPoint` into an isomorphism of
relative groups in every degree.  This is `CharClass/LIXSectionLocalHomeo.lean` +
`LIXSectionChartPair.lean` with the rank a parameter and the constant section at `e₀`.

By `CharClass/LIXKGenSect.lean`'s `joinC_kSect`, the section read in the chart at the `j`-th of
the `k+1` zeros is this same trivial block, so one local model serves every zero.

## Main results

* `KGen.eulerLocalHomeo`, `zero_mem_eulerLocalHomeo_source`, `zero_mem_eulerLocalHomeo_target`,
  `eulerLocalHomeo_zero`.
* `KGen.lixChartPairHomeo`, `KGen.lixLocalRelIso`, `injective_lixLocalRelIso`.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open CategoryTheory

set_option linter.unusedSectionVars false

/-! ## 1. The local homeomorphism -/

/-- **The local homeomorphism at the zero**, at rank `n`. -/
def eulerLocalHomeo (n : ℕ) : OpenPartialHomeomorph (ChartSrc n) (Fin (n + 1) → ℂ) :=
  (hasStrictFDerivAt_trivialBlockChart n).toOpenPartialHomeomorph
    (fun p : ChartSrc n => trivialBlockChart n p.1 p.2)

theorem eulerLocalHomeo_coe (n : ℕ) :
    (eulerLocalHomeo n : ChartSrc n → (Fin (n + 1) → ℂ))
      = fun p => trivialBlockChart n p.1 p.2 :=
  (hasStrictFDerivAt_trivialBlockChart n).toOpenPartialHomeomorph_coe

theorem zero_mem_eulerLocalHomeo_source (n : ℕ) :
    (0 : ChartSrc n) ∈ (eulerLocalHomeo n).source :=
  (hasStrictFDerivAt_trivialBlockChart n).mem_toOpenPartialHomeomorph_source

theorem eulerLocalHomeo_zero (n : ℕ) :
    eulerLocalHomeo n (0 : ChartSrc n) = (0 : Fin (n + 1) → ℂ) := by
  rw [show eulerLocalHomeo n (0 : ChartSrc n)
      = (fun p : ChartSrc n => trivialBlockChart n p.1 p.2) 0 from
    congrFun (eulerLocalHomeo_coe n) 0]
  exact trivialBlockChart_zero n

theorem zero_mem_eulerLocalHomeo_target (n : ℕ) :
    (0 : Fin (n + 1) → ℂ) ∈ (eulerLocalHomeo n).target := by
  have h := (hasStrictFDerivAt_trivialBlockChart n).image_mem_toOpenPartialHomeomorph_target
  rwa [show trivialBlockChart n (0 : ChartSrc n).1 (0 : ChartSrc n).2 = (0 : Fin (n + 1) → ℂ)
    from trivialBlockChart_zero n] at h

/-! ## 2. The punctured pair and its relative groups -/

/-- **The section's chart at rank `n`, as a homeomorphism of punctured pairs.** -/
def lixChartPairHomeo (n : ℕ) :
    ↥((Subtype.val : ↥(eulerLocalHomeo n).source → ChartSrc n) ⁻¹' ({0}ᶜ : Set (ChartSrc n)))
      ≃ₜ ↥((Subtype.val : ↥(eulerLocalHomeo n).target → (Fin (n + 1) → ℂ)) ⁻¹'
        ({0}ᶜ : Set (Fin (n + 1) → ℂ))) :=
  openPartialHomeomorphChartPair (eulerLocalHomeo n) (zero_mem_eulerLocalHomeo_source n)
    (zero_mem_eulerLocalHomeo_target n) (eulerLocalHomeo_zero n)

/-- **The chart identifies the two relative groups, in every degree.** -/
def lixLocalRelIso (n m : ℕ) :
    relCohomology (ZMod 2) (TopCat.of ↥(eulerLocalHomeo n).source)
        ((Subtype.val : ↥(eulerLocalHomeo n).source → ChartSrc n) ⁻¹'
          ({0}ᶜ : Set (ChartSrc n))) m
      ≅ relCohomology (ZMod 2) (TopCat.of ↥(eulerLocalHomeo n).target)
        ((Subtype.val : ↥(eulerLocalHomeo n).target → (Fin (n + 1) → ℂ)) ⁻¹'
          ({0}ᶜ : Set (Fin (n + 1) → ℂ))) m :=
  relCohomologyCongrPoint (eulerLocalHomeo n).toHomeomorphSourceTarget
    (zero_mem_eulerLocalHomeo_source n) (zero_mem_eulerLocalHomeo_target n)
    (Subtype.ext (by simp [eulerLocalHomeo_zero])) m

theorem injective_lixLocalRelIso (n m : ℕ) :
    Function.Injective (lixLocalRelIso n m).hom.hom := by
  intro a b hab
  rw [← iso_inv_hom_apply (lixLocalRelIso n m) a, ← iso_inv_hom_apply (lixLocalRelIso n m) b,
    hab]

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.eulerLocalHomeo_zero
#audit_axioms KGen.zero_mem_eulerLocalHomeo_target
#audit_axioms KGen.injective_lixLocalRelIso

end GroupApproximation.CharClass
