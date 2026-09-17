import GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.Leaf
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence carriers of `sec:torsion-free` over the five open residuals

`non_mf_groups_exist.tex`, Section `sec:torsion-free`, tex lines 2122–2182: the paragraph after
`thm:hull` (line 2129), the proof of `lem:saturation` (line 2144) and the proof of
`thm:torsion-free` (line 2182), plus `thm:hull` at Osin's notion over a torsion-free group
(line 2122) and the Fournier-Facio citation of Hull's Corollary 7.4 (the paragraph after the proof
of `lem:saturation`).

The statements are the seven statements of `TorsionFreeGreendlingerSentences`, unchanged, with
their printed binders.  Only the hypothesis changes: `hgreendlinger` (the whole least-area leaf)
is replaced by `hopen : AsmWaist.GreendlingerOpenResidualsBelowStatement.{0,0,0}`, the five open
residuals of the Below Greendlinger waist, which is strictly smaller in proof content (see
`GreendlingerClosedSteps/Leaf`).

## Route

Each body is the matching `TorsionFreeGreendlingerSentences.*_of_greendlinger` theorem applied to
`GreendlingerClosedSteps.leastAreaLeaf_of_openResidualsBelow hopen` and the printed binders.

The name `manuscriptSentence_saturationPairAndHullAgain_of_openResidualsBelow` is taken by the
printed-proposition carrier in `GreendlingerClosedSteps/Paragraphs`, so the Cayley-graph,
torsion-free form here carries the suffix `TorsionFree`.

## Manuscript status

`partial` until lane gl-assembly-04 produces the five residuals.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace GreendlingerClosedSteps

section HullParagraph

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **"Hull's proof treats $m=1$ by passing to $G/\normal{r}_G$ for one element $r$"** (tex line
2129), at every ambient group, over the five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_hullOneTargetOneRelatorGeneral_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0})
    {G : Type} [Group G] (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) (t : G) :
    ∃ (s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) (fun _ : Fin 1 => t) 0)
      (r : G), s.step.q.ker = Subgroup.normalClosure ({r} : Set G) ∧
        Nonempty (G ⧸ Subgroup.normalClosure ({r} : Set G) ≃* s.step.Q) :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen) A hN t

/-- **"and the general case by induction on $m$, using his clause~(d), that $\varphi(N)$ is
again suitable"** (tex line 2129), at every ambient group, over the five open residuals of the
Below Greendlinger waist. -/
theorem manuscriptSentence_hullInductionOnTargetsGeneral_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0})
    (m : ℕ) {G : Type} [Group G] (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) (t : Fin m → G) (R : ℕ) :
    ∃ s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) t R,
      Suitable s.step.hullSet.alphabet (N.map s.step.q) :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_hullInductionOnTargetsGeneral_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen) m A hN t R

end HullParagraph

section Saturation

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.Manuscript.NonMF.HullCorrectedInputs

/-- **`thm:hull` at Osin's notion over a torsion-free ambient group** (tex line 2122,
`\label{thm:hull}`), over the five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_hullTheoremTorsionFreeOsin_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    ∀ (G : Type) [Group G], GGT.IsAcylindricallyHyperbolicOsin G →
      IsPowerTorsionFree G →
        ∀ (A : HullGeneratingSet G) {N : Subgroup G}, Suitable A.alphabet N →
          ∀ {m : ℕ} (g : Fin m → G),
            ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
              GGT.IsAcylindricallyHyperbolicOsin Q ∧ (∀ i : Fin m, φ (g i) ∈ N.map φ) ∧
                ∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_hullTheoremTorsionFreeOsin_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

/-- **"By Hull [Corollary 5.7 and Lemma 5.8], `N` contains two elements `h₁,h₂` such that
`N₀ = ⟨h₁,h₂⟩` is suitable with respect to a generating set `A' ⊇ A` to which Hull's small
cancellation theorem again applies"** (tex line 2144, in the proof of `\label{lem:saturation}`),
over the five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_saturationPairAndHullAgainTorsionFree_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0})
    {G : Type} [Group G] [IsAcylindricallyHyperbolic G] (hG : IsPowerTorsionFree G)
    (A : HullGeneratingSet G) {N : Subgroup G} (hN : Suitable A.alphabet N) :
    ∃ A' : HullGeneratingSet G, A.alphabet.carrier ⊆ A'.alphabet.carrier ∧
      ∃ h₁ ∈ N, ∃ h₂ ∈ N,
        Suitable A'.alphabet (Subgroup.closure ({h₁, h₂} : Set G)) ∧
          ∀ {m : ℕ} (g : Fin m → G),
            Nonempty (HullQuotientNG (Subgroup.closure ({h₁, h₂} : Set G)) g
              (∅ : Set G)) :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_saturationPairAndHullAgain_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen) hG A hN

/-- **"Apply Theorem `thm:hull` to `N₀`, with respect to `A'`, with `g₁,…,g_m` a finite
generating set of `G`"** (tex line 2144, in the proof of `\label{lem:saturation}`), with the
kernel datum, over the five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_saturationApplyHullNoOmega_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0})
    {G : Type} [Group G] [Group.IsFinitelyPresented G] [IsAcylindricallyHyperbolic G]
    (hG : IsPowerTorsionFree G) (A' : HullGeneratingSet G) {N₀ : Subgroup G}
    (hN₀ : Suitable A'.alphabet N₀) :
    ∃ (m : ℕ) (g : Fin m → G), Subgroup.closure (Set.range g) = ⊤ ∧
      Nonempty (HullQuotientNG N₀ g (∅ : Set G)) :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_saturationApplyHullNoOmega_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen) hG A' hN₀

/-- **"By Lemma `lem:saturation` applied to `G₀` and `N`, there is a surjective homomorphism
`φ : G₀ → Q` with `Q` two-generated, finitely presented, torsion-free, and acylindrically
hyperbolic, and `φ(N) = Q`"** (tex line 2182, in the proof of `\label{thm:torsion-free}`), with
no finite set, over the five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_theoremApplySaturationNoOmega_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0})
    {G₀ : Type} [Group G₀] [Group.IsFinitelyPresented G₀] [IsAcylindricallyHyperbolic G₀]
    (hG₀ : IsPowerTorsionFree G₀) (N : Subgroup G₀) [N.Normal] (hN : N ≠ ⊥) :
    Nonempty (SaturationQuotient N (∅ : Set G₀)) :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_theoremApplySaturationNoOmega_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen) hG₀ N hN

end Saturation

section HullCitation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

/-- **"The group $G_0$ is obtained there as a common quotient of two finitely generated
acylindrically hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the
quotient to be chosen acylindrically hyperbolic"** (the Fournier-Facio paragraph after the proof
of `lem:saturation`), over the five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_hullCommonQuotient_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    HullCommonQuotientPrinted :=
  TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

end HullCitation

end GreendlingerClosedSteps
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_openResidualsBelow
#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.manuscriptSentence_hullInductionOnTargetsGeneral_of_openResidualsBelow
#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.manuscriptSentence_hullTheoremTorsionFreeOsin_of_openResidualsBelow
#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.manuscriptSentence_saturationPairAndHullAgainTorsionFree_of_openResidualsBelow
#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.manuscriptSentence_saturationApplyHullNoOmega_of_openResidualsBelow
#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.manuscriptSentence_theoremApplySaturationNoOmega_of_openResidualsBelow
#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.manuscriptSentence_hullCommonQuotient_of_openResidualsBelow
