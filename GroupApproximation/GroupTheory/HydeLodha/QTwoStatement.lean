import GroupApproximation.GroupTheory.HydeLodha.GammaTwoSimple
import GroupApproximation.GroupTheory.HydeLodha.GammaOrbitsZero
import GroupApproximation.Manuscript.NonMF.FournierFacioParagraphFromSimpleFactor
import GroupApproximation.Meta.AxiomGuard

/-!
# `Q₂` for `FinitelyPresentedInfiniteSimpleStatement`

Hyde–Lodha, Theorem 1.3: "`Q_n = [Γ_n, Γ_n]` is a finitely presented simple group of
orientation-preserving homeomorphisms of `ℝ`".  For `n = 2`:

* `isSimpleGroup_qTwo_closed`: Proposition 3.11, with the residue congruence of Lemma 3.8 at `0`
  (`gammaTwo_resEq_apply_zero`) discharged, so it has no hypothesis;
* `qTwo_torsionFree`, `infinite_qTwo` (`GammaTwoSimple`);
* `finitelyPresentedInfiniteSimpleStatement_of_isFinitelyPresented_qTwo`: the statement the
  manuscript's Fournier-Facio paragraph cites, from Theorem 4.8 (`Q₂` finitely presented), which is
  the one remaining explicit hypothesis.
-/

namespace GroupApproximation
namespace HydeLodha

open Manuscript.NonMF.TorsionFreePrinted

/-- **Hyde–Lodha, Proposition 3.11, at `n = 2`.** -/
theorem isSimpleGroup_qTwo_closed : IsSimpleGroup ↥qTwo :=
  isSimpleGroup_qTwo fun _ hf h0 h1 => gammaTwo_resEq_apply_zero hf h0 h1

/-- **The torsion-free infinite simple group `Q₂`, given Theorem 4.8.** -/
theorem finitelyPresentedInfiniteSimpleStatement_of_isFinitelyPresented_qTwo
    (hfp : Group.IsFinitelyPresented ↥qTwo) : FinitelyPresentedInfiniteSimpleStatement :=
  ⟨↥qTwo, inferInstance, hfp, qTwo_torsionFree, isSimpleGroup_qTwo_closed, infinite_qTwo⟩

#audit_closed_axioms GroupApproximation.HydeLodha.isSimpleGroup_qTwo_closed
#audit_axioms GroupApproximation.HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_isFinitelyPresented_qTwo

end HydeLodha
end GroupApproximation
