import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences
import GroupApproximation.Manuscript.NonMF.TorsionFreeLeastAreaAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence carriers for `sec:torsion-free`, over the least-area leaves

`TorsionFreeSectionSentences` carries the proof sentences of `lem:saturation` and
`thm:torsion-free` that rest on Hull's Theorem 7.1 over the historical Greendlinger
waist and the control form of Osin's Lemma 5.1.  The section's Hull chain now runs
over the two least-area leaves:

* `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`, Osin's
  Lemma 4.4 at least-area diagrams;
* `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`, Osin's Lemma
  5.1 in the embedded form.

This module restates those sentences over them (`TorsionFreeLeastAreaAssembly`).
The pair `h₁, h₂` and the finite generating family are closed exactly as before.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeSectionSentencesLeastArea

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.Manuscript.NonMF.HullCorrectedInputs

/-- **"By Hull [Corollary 5.7 and Lemma 5.8], `N` contains two elements
`h₁,h₂` such that `N₀ = ⟨h₁,h₂⟩` is suitable with respect to a generating set
`A' ⊇ A` to which Hull's small cancellation theorem again applies"** (tex line 1662),
over the least-area leaves.  Over a torsion-free ambient group the pair is a theorem
with `A' = A`; the last clause is `thm:hull` at `A'`. -/
theorem manuscriptSentence_saturationPairAndHullAgain_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    {G : Type} [Group G] [IsAcylindricallyHyperbolic G] (hG : IsPowerTorsionFree G)
    (A : HullGeneratingSet G) {N : Subgroup G} (hN : Suitable A.alphabet N) :
    ∃ A' : HullGeneratingSet G, A.alphabet.carrier ⊆ A'.alphabet.carrier ∧
      ∃ h₁ ∈ N, ∃ h₂ ∈ N,
        Suitable A'.alphabet (Subgroup.closure ({h₁, h₂} : Set G)) ∧
          ∀ {m : ℕ} (g : Fin m → G),
            Nonempty (HullQuotientNG (Subgroup.closure ({h₁, h₂} : Set G)) g
              (∅ : Set G)) := by
  obtain ⟨A', hA', h₁, hh₁, h₂, hh₂, hsuit⟩ := hullSuitablePair_of_torsionFree hG A hN
  exact ⟨A', hA', h₁, hh₁, h₂, hh₂, hsuit, fun g =>
    TorsionFreeLeastAreaAssembly.hullSmallCancellationTorsionFreePrinted_of_leastAreaLeaves
      hgreendlinger hbridge hG A' hsuit g⟩

/-- **"Apply Theorem `thm:hull` to `N₀`, with respect to `A'`, with
`g₁,…,g_m` a finite generating set of `G`"** (tex line 1665), over the least-area
leaves, with the kernel datum. -/
theorem manuscriptSentence_saturationApplyHullNoOmega_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    {G : Type} [Group G] [Group.IsFinitelyPresented G] [IsAcylindricallyHyperbolic G]
    (hG : IsPowerTorsionFree G) (A' : HullGeneratingSet G) {N₀ : Subgroup G}
    (hN₀ : Suitable A'.alphabet N₀) :
    ∃ (m : ℕ) (g : Fin m → G), Subgroup.closure (Set.range g) = ⊤ ∧
      Nonempty (HullQuotientNG N₀ g (∅ : Set G)) := by
  obtain ⟨m, g, htop⟩ := exists_finite_generating_family G
  exact ⟨m, g, htop,
    TorsionFreeLeastAreaAssembly.hullSmallCancellationTorsionFreePrinted_of_leastAreaLeaves
      hgreendlinger hbridge hG A' hN₀ g⟩

/-- **"By Lemma `lem:saturation` applied to `G₀` and `N`, there is a surjective
homomorphism `φ : G₀ → Q` with `Q` two-generated, finitely presented,
torsion-free, and acylindrically hyperbolic, and `φ(N) = Q`"** (tex line 1698),
over the least-area leaves, with no finite set. -/
theorem manuscriptSentence_theoremApplySaturationNoOmega_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    {G₀ : Type} [Group G₀] [Group.IsFinitelyPresented G₀] [IsAcylindricallyHyperbolic G₀]
    (hG₀ : IsPowerTorsionFree G₀) (N : Subgroup G₀) [N.Normal] (hN : N ≠ ⊥) :
    Nonempty (SaturationQuotient N (∅ : Set G₀)) :=
  TorsionFreeLeastAreaAssembly.printedSaturationNoOmega_of_leastAreaLeaves
    hgreendlinger hbridge G₀ hG₀ N hN

end TorsionFreeSectionSentencesLeastArea
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentencesLeastArea.manuscriptSentence_saturationPairAndHullAgain_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentencesLeastArea.manuscriptSentence_saturationApplyHullNoOmega_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentencesLeastArea.manuscriptSentence_theoremApplySaturationNoOmega_of_leastAreaLeaves
