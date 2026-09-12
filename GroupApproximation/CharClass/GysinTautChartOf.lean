import GroupApproximation.CharClass.GysinRetractOf
import GroupApproximation.CharClass.ChernEulerBundleOf
import GroupApproximation.CharClass.LerayHirschChartClassK
import GroupApproximation.Meta.AxiomGuard

/-!
# The tautological class dies on the chart, over any field

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`GysinTautFields.rChart_tautEuler` shows at `F₂` that the chart reading of the tautological
class of `P(p ⊕ 1)` vanishes: pulled back along the zero section the tautological line is
constant, so its classifying map factors through a point, which has no `H²`.  Nothing there
uses the coefficient.  Over a field `K` the Euler class of a line bundle is the pullback of a
chosen generator `hgen : H²(ℂP^d; K)` along the classifying map (`lix-lh`'s
`eulerOfBundleOf`), and the vanishing holds for every choice of `hgen`, because the
classifying map factors through a point whatever the generator.

## Main declarations

* `rChartOf_tautEulerK` — **the tautological class dies on the chart, over a field**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace Gysin

open CategoryTheory TopologicalSpace

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The tautological class dies on the chart, over a field**, for every choice of the
degree-two generator of `ℂP^d`.  The only geometric input is the identification of the
chart's section with the zero section. -/
theorem rChartOf_tautEulerK (K : Type) [Field K] [Nonempty X] (p : Bundle X ι)
    (hsec : IsZeroSectionChart p) (hgen : Hmod K (CPtop (1 + LH.tautCard ι)) 2) :
    rChartOf K p 2 (LH.tautEulerK K hgen p) = 0 := by
  classical
  have hqt : ∀ x, ((Bundle.pushforward (LH.tautEmb ι) (LH.tautEmb_injective ι)
      (Bundle.comap (Bundle.zeroSectionProj p) (Bundle.tautLine p.plusOne))) x).trace = 1 :=
    fun x => CPn.trace_pushforward_one (LH.tautEmb ι) (LH.tautEmb_injective ι) _
      (fun y => Bundle.trace_tautLine p.plusOne (Bundle.zeroSectionProj p y)) x
  have hstep : rChartOf K p 2 (LH.tautEulerK K hgen p)
      = eulerOfBundleOf K hgen
          (Bundle.pushforward (LH.tautEmb ι) (LH.tautEmb_injective ι)
            (Bundle.comap (Bundle.zeroSectionProj p) (Bundle.tautLine p.plusOne))) hqt := by
    rw [rChartOf_eq, hsec, LH.tautEulerK, ← eulerOfBundle_comapOf]
    rfl
  rw [hstep]
  refine eulerOfBundle_eq_zero_of_factorsOf K hgen _ hqt
    (P := TopCat.of PUnit) (cmap ⟨fun _ => PUnit.unit, continuous_const⟩)
    (cmap (ContinuousMap.const PUnit
      (Bundle.classifyOne _ hqt (Classical.arbitrary X)))) ?_ ?_
  · exact TopCat.hom_ext (ContinuousMap.ext fun _ => Subtype.ext rfl)
  · exact fun a => (hasPointCohomology_of_contractibleOf K PUnit).2 2 (by omega) a

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms rChartOf_tautEulerK

end

end Gysin
end CharClass
end GroupApproximation
