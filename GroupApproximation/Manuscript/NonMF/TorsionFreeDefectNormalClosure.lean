import GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# The normal closure of `φ(S)` in the proof of `thm:torsion-free`

`non_mf_groups_exist.tex`, proof of `thm:torsion-free` (tex lines 1705–1709):

> The subgroup `𝔇_Q(φ(Γ))` is normal in `Q`, and the normal closure of `φ(S)` is
> `φ(N) = Q`, so `𝔇_Q(φ(Γ)) = Q`.

`TorsionFreePrintedSentences.manuscriptSentence_theoremDefectEqTop` carries the first
clause and the conclusion, but it reaches the conclusion by pulling the defect back
along `φ`.  The middle clause, that the normal closure of `φ(S)` is `φ(N)`, is in
neither its statement nor its proof.  This module states the sentence with all three
clauses and proves the conclusion along the printed route:

* `φ` is the surjection of `lem:saturation`, so the normal closure of `φ(S)` is
  `φ(N)`, where `N` is the normal closure of `S` (`Subgroup.map_normalClosure`);
* `φ(N) = Q` is the last conclusion of `lem:saturation`;
* `𝔇_Q(φ(Γ))` is normal and contains `φ(S)` by the previous sentence
  (`manuscriptSentence_theoremDefectFunctorial`), so it contains the normal closure
  of `φ(S)`, which is `Q`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeDefectNormalClosure

/-- **`thm:torsion-free`, printed sentence, every clause.**

> The subgroup `𝔇_Q(φ(Γ))` is normal in `Q`, and the normal closure of `φ(S)` is
> `φ(N) = Q`, so `𝔇_Q(φ(Γ)) = Q`.

`S = tJt⁻¹` is `F.conjFactor`, `Γ` is `F.core`, and `N` is the normal closure of `S`
in `G₀`.  The surjection `φ` and `φ(N) = Q` come from `lem:saturation`, applied in the
preceding sentence of the proof. -/
theorem manuscriptSentence_theoremNormalClosureDefectEqTop {G₀ : Type} [Group G₀]
    (F : PrintedFournierFacioData G₀) {Q : Type} [Group Q] (phi : G₀ →* Q)
    (hphi : Function.Surjective phi)
    (hN : (Subgroup.normalClosure (F.conjFactor : Set G₀)).map phi = ⊤) :
    (OneSidedMFRadical.printedDefect (F.core.map phi)).Normal ∧
      Subgroup.normalClosure ((F.conjFactor.map phi : Subgroup Q) : Set Q) =
        (Subgroup.normalClosure (F.conjFactor : Set G₀)).map phi ∧
      (Subgroup.normalClosure (F.conjFactor : Set G₀)).map phi = ⊤ ∧
      OneSidedMFRadical.printedDefect (F.core.map phi) = ⊤ := by
  have hcl : Subgroup.normalClosure ((F.conjFactor.map phi : Subgroup Q) : Set Q) =
      (Subgroup.normalClosure (F.conjFactor : Set G₀)).map phi := by
    rw [Subgroup.coe_map, Subgroup.map_normalClosure (F.conjFactor : Set G₀) phi hphi]
  refine ⟨inferInstance, hcl, hN, ?_⟩
  refine top_unique ?_
  rw [← hN, ← hcl]
  exact Subgroup.normalClosure_le_normal
    (SetLike.coe_subset_coe.mpr
      (TorsionFreePrintedSentences.manuscriptSentence_theoremDefectFunctorial F phi))

/-- The sentence as a closed proposition: the Fournier-Facio datum, the target group,
the surjection `φ` and `φ(N) = Q` are all quantified inside. -/
def PrintedNormalClosureDefectEqTop : Prop :=
  ∀ {G₀ : Type} [Group G₀] (F : PrintedFournierFacioData G₀) {Q : Type} [Group Q]
    (phi : G₀ →* Q), Function.Surjective phi →
    (Subgroup.normalClosure (F.conjFactor : Set G₀)).map phi = ⊤ →
    (OneSidedMFRadical.printedDefect (F.core.map phi)).Normal ∧
      Subgroup.normalClosure ((F.conjFactor.map phi : Subgroup Q) : Set Q) =
        (Subgroup.normalClosure (F.conjFactor : Set G₀)).map phi ∧
      (Subgroup.normalClosure (F.conjFactor : Set G₀)).map phi = ⊤ ∧
      OneSidedMFRadical.printedDefect (F.core.map phi) = ⊤

/-- **"The subgroup `𝔇_Q(φ(Γ))` is normal in `Q`, and the normal closure of `φ(S)` is
`φ(N) = Q`, so `𝔇_Q(φ(Γ)) = Q`."**  Closed. -/
theorem printedNormalClosureDefectEqTop : PrintedNormalClosureDefectEqTop := by
  intro G₀ _ F Q _ phi hphi hN
  exact manuscriptSentence_theoremNormalClosureDefectEqTop F phi hphi hN

end TorsionFreeDefectNormalClosure
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeDefectNormalClosure.manuscriptSentence_theoremNormalClosureDefectEqTop
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeDefectNormalClosure.printedNormalClosureDefectEqTop
