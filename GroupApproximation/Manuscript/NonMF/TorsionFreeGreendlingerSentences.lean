import GroupApproximation.GGT.HullSCLemma51EmbeddedBridgeHolds
import GroupApproximation.Manuscript.NonMF.HullCitationSentences
import GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedLeastArea
import GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion
import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentencesLeastArea
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence carriers of `sec:torsion-free` over the least-area Greendlinger leaf alone

The proof sentences of `thm:hull`, `lem:saturation` and `thm:torsion-free` over the least-area
leaves take the Greendlinger waist `hgreendlinger` and the embedded bridge `hbridge`.  The bridge
is proved by `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`
(`GGT/HullSCLemma51EmbeddedBridgeHolds.lean`), so each sentence here applies it and stands over
`hgreendlinger` alone.  The statements are those of `TorsionFreeHullPrintedLeastArea`,
`TorsionFreeSectionSentencesLeastArea`, `TorsionFreeOsinNotion` and `HullCitationSentences`,
unchanged.

The printed endpoints over the same leaf are in `TorsionFreeGreendlingerLeaf`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeGreendlingerSentences

section HullParagraph

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **"Hull's proof treats $m=1$ by passing to $G/\normal{r}_G$ for one element $r$"** (tex line
1644, the paragraph after `\label{thm:hull}`), at every ambient group, over the least-area
Greendlinger leaf alone. -/
theorem manuscriptSentence_hullOneTargetOneRelatorGeneral_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    {G : Type} [Group G] (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) (t : G) :
    ∃ (s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) (fun _ : Fin 1 => t) 0)
      (r : G), s.step.q.ker = Subgroup.normalClosure ({r} : Set G) ∧
        Nonempty (G ⧸ Subgroup.normalClosure ({r} : Set G) ≃* s.step.Q) :=
  TorsionFreeHullParagraphGeneral.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_leastAreaLeaves
    hgreendlinger HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed A hN t

/-- **"and the general case by induction on $m$, using his clause~(d), that $\varphi(N)$ is
again suitable"** (tex line 1644, the paragraph after `\label{thm:hull}`), at every ambient
group, over the least-area Greendlinger leaf alone. -/
theorem manuscriptSentence_hullInductionOnTargetsGeneral_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (m : ℕ) {G : Type} [Group G] (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) (t : Fin m → G) (R : ℕ) :
    ∃ s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) t R,
      Suitable s.step.hullSet.alphabet (N.map s.step.q) :=
  TorsionFreeHullParagraphGeneral.manuscriptSentence_hullInductionOnTargetsGeneral_of_leastAreaLeaves
    hgreendlinger HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed m A hN t R

end HullParagraph

section Saturation

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.Manuscript.NonMF.HullCorrectedInputs

/-- **`thm:hull` at Osin's notion over a torsion-free ambient group** (tex line 1636,
`\label{thm:hull}`), over the least-area Greendlinger leaf alone. -/
theorem manuscriptSentence_hullTheoremTorsionFreeOsin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    ∀ (G : Type) [Group G], GGT.IsAcylindricallyHyperbolicOsin G →
      IsPowerTorsionFree G →
        ∀ (A : HullGeneratingSet G) {N : Subgroup G}, Suitable A.alphabet N →
          ∀ {m : ℕ} (g : Fin m → G),
            ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
              GGT.IsAcylindricallyHyperbolicOsin Q ∧ (∀ i : Fin m, φ (g i) ∈ N.map φ) ∧
                ∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y :=
  TorsionFreeOsinNotion.manuscriptSentence_hullTheoremTorsionFreeOsin_of_leastAreaLeaves
    hgreendlinger HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

/-- **"By Hull [Corollary 5.7 and Lemma 5.8], `N` contains two elements `h₁,h₂` such that
`N₀ = ⟨h₁,h₂⟩` is suitable with respect to a generating set `A' ⊇ A` to which Hull's small
cancellation theorem again applies"** (tex line 1662, in the proof of `\label{lem:saturation}`),
over the least-area Greendlinger leaf alone. -/
theorem manuscriptSentence_saturationPairAndHullAgain_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    {G : Type} [Group G] [IsAcylindricallyHyperbolic G] (hG : IsPowerTorsionFree G)
    (A : HullGeneratingSet G) {N : Subgroup G} (hN : Suitable A.alphabet N) :
    ∃ A' : HullGeneratingSet G, A.alphabet.carrier ⊆ A'.alphabet.carrier ∧
      ∃ h₁ ∈ N, ∃ h₂ ∈ N,
        Suitable A'.alphabet (Subgroup.closure ({h₁, h₂} : Set G)) ∧
          ∀ {m : ℕ} (g : Fin m → G),
            Nonempty (HullQuotientNG (Subgroup.closure ({h₁, h₂} : Set G)) g
              (∅ : Set G)) :=
  TorsionFreeSectionSentencesLeastArea.manuscriptSentence_saturationPairAndHullAgain_of_leastAreaLeaves
    hgreendlinger HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed hG A hN

/-- **"Apply Theorem `thm:hull` to `N₀`, with respect to `A'`, with `g₁,…,g_m` a finite
generating set of `G`"** (tex line 1665, in the proof of `\label{lem:saturation}`), with the
kernel datum, over the least-area Greendlinger leaf alone. -/
theorem manuscriptSentence_saturationApplyHullNoOmega_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    {G : Type} [Group G] [Group.IsFinitelyPresented G] [IsAcylindricallyHyperbolic G]
    (hG : IsPowerTorsionFree G) (A' : HullGeneratingSet G) {N₀ : Subgroup G}
    (hN₀ : Suitable A'.alphabet N₀) :
    ∃ (m : ℕ) (g : Fin m → G), Subgroup.closure (Set.range g) = ⊤ ∧
      Nonempty (HullQuotientNG N₀ g (∅ : Set G)) :=
  TorsionFreeSectionSentencesLeastArea.manuscriptSentence_saturationApplyHullNoOmega_of_leastAreaLeaves
    hgreendlinger HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed hG A' hN₀

/-- **"By Lemma `lem:saturation` applied to `G₀` and `N`, there is a surjective homomorphism
`φ : G₀ → Q` with `Q` two-generated, finitely presented, torsion-free, and acylindrically
hyperbolic, and `φ(N) = Q`"** (tex line 1698, in the proof of `\label{thm:torsion-free}`), with
no finite set, over the least-area Greendlinger leaf alone. -/
theorem manuscriptSentence_theoremApplySaturationNoOmega_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    {G₀ : Type} [Group G₀] [Group.IsFinitelyPresented G₀] [IsAcylindricallyHyperbolic G₀]
    (hG₀ : IsPowerTorsionFree G₀) (N : Subgroup G₀) [N.Normal] (hN : N ≠ ⊥) :
    Nonempty (SaturationQuotient N (∅ : Set G₀)) :=
  TorsionFreeSectionSentencesLeastArea.manuscriptSentence_theoremApplySaturationNoOmega_of_leastAreaLeaves
    hgreendlinger HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed hG₀ N hN

end Saturation

section HullCitation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

/-- **"The group $G_0$ is obtained there as a common quotient of two finitely generated
acylindrically hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the
quotient to be chosen acylindrically hyperbolic"** (tex lines 1680-1683, in the Fournier-Facio
paragraph at line 1675, which precedes the proof of `thm:torsion-free` at line 1696;
`\label{thm:torsion-free}` is at line 284), over the least-area Greendlinger leaf alone. -/
theorem manuscriptSentence_hullCommonQuotient_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    HullCommonQuotientPrinted :=
  HullCitationSentences.manuscriptSentence_hullCommonQuotient_of_leastAreaLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

end HullCitation

end TorsionFreeGreendlingerSentences
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullInductionOnTargetsGeneral_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullTheoremTorsionFreeOsin_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_saturationPairAndHullAgain_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_saturationApplyHullNoOmega_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_theoremApplySaturationNoOmega_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullCommonQuotient_of_greendlinger
