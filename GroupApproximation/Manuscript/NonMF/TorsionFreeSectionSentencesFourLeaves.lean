import GroupApproximation.GGT.OsinLimitSetSpelling
import GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedLeastArea
import GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetNotion
import GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences
import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentencesLeastArea
import GroupApproximation.Meta.AxiomGuard

/-!
# Proof-step sentences of `sec:torsion-free` as named propositions over the walls

`non_mf_groups_exist.tex`, Section `sec:torsion-free` (tex lines 1621–1737).  Four
proof-step sentences of the section rest on Hull's Theorem 7.1:

* the paragraph after `thm:hull` on the shape of Hull's proof (tex lines 1644–1648);
* in the proof of `lem:saturation`, the pair `h₁, h₂` "to which Hull's small
  cancellation theorem again applies" (tex lines 1662–1665);
* in the same proof, the application of `thm:hull` to `N₀` (tex lines 1665–1667);
* in the proof of `thm:torsion-free`, the application of `lem:saturation` to `G₀`
  and `N` (tex lines 1698–1701).

`TorsionFreeHullPrintedLeastArea` and `TorsionFreeSectionSentencesLeastArea` carry
these sentences at Hull's Cayley-graph notion.  This module states each as a named
proposition at the manuscript's notion of acylindrical hyperbolicity, the limit-set
notion `GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet`, and proves it
from the walls.  The hard direction of Osin's Theorem 1.1 is no longer a
hypothesis: it is `GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet`.

Of the four walls of the top endpoints these sentences use exactly two, the
least-area Greendlinger waist
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` and the embedded
bridge `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`.
Kotowski–Ollivier and a finitely presented infinite simple group do not enter, so
the `_of_fourLeaves` forms take only these two.  Once both walls have closed
producers, each proposition is a closed theorem in one line.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeSectionSentencesFourLeaves

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.ReducedGroupCStarTrace
open GroupApproximation.GroupVonNeumann

/-! ## The paragraph after `thm:hull` (tex lines 1644–1648) -/

/-- **The paragraph after `thm:hull`, as printed** (tex lines 1644–1648).

> Hull's proof treats `m = 1` by passing to `G/⟨⟨r⟩⟩_G` for one element `r` and
> the general case by induction on `m`, using his clause (d), that `φ(N)` is
> again suitable [Hull, proof of Theorem 7.1], so `ker φ` is the normal closure
> of `m` elements and `Q` is finitely presented when `G` is.

For `G` acylindrically hyperbolic, `A` Hull's generating set and `N` suitable
with respect to `A` (the hypotheses of `thm:hull`, tex lines 1637–1638):

* at one target `t`, the kernel of Hull's quotient is `⟨⟨r⟩⟩_G` for one element
  `r`, and the quotient is `G/⟨⟨r⟩⟩_G`;
* at `m` targets, the quotient of the induction exists, `φ(N)` is again suitable
  (clause (d)), `ker φ` is the normal closure of at most `m` elements, and `Q` is
  finitely presented when `G` is.

`HullSC.HullTower` is the quotient of Hull's construction with the clauses of
`thm:hull`. -/
def PrintedHullProofParagraph : Prop :=
  ∀ {G : Type} [Group G], GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G →
    ∀ (A : HullGeneratingSet G) {N : Subgroup G}, Suitable A.alphabet N →
      (∀ t : G,
        ∃ (s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) (fun _ : Fin 1 => t) 0)
          (r : G), s.step.q.ker = Subgroup.normalClosure ({r} : Set G) ∧
            Nonempty (G ⧸ Subgroup.normalClosure ({r} : Set G) ≃* s.step.Q)) ∧
      ∀ {m : ℕ} (t : Fin m → G),
        ∃ s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) t 0,
          Suitable s.step.hullSet.alphabet (N.map s.step.q) ∧
            (∃ T : Finset G, T.card ≤ m ∧
              s.step.q.ker = Subgroup.normalClosure (T : Set G)) ∧
              (Group.IsFinitelyPresented G → Group.IsFinitelyPresented s.step.Q)

open TorsionFreeHullParagraphGeneral in
/-- **The paragraph after `thm:hull`, from the walls it uses**: the least-area
Greendlinger waist and the embedded bridge. -/
theorem printedHullProofParagraph_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedHullProofParagraph := by
  intro G _ _hG A N hN
  refine ⟨fun t =>
    manuscriptSentence_hullOneTargetOneRelatorGeneral_of_leastAreaLeaves
      hgreendlinger hbridge A hN t, ?_⟩
  intro m t
  obtain ⟨s, hs⟩ :=
    manuscriptSentence_hullInductionOnTargetsGeneral_of_leastAreaLeaves
      hgreendlinger hbridge m A hN t 0
  exact ⟨s, hs, TorsionFreeSectionSentences.manuscriptSentence_hullKernelRemark s⟩

/-! ## The proof of `lem:saturation` (tex lines 1658–1673) -/

/-- **"By Hull [Corollary 5.7 and Lemma 5.8], `N` contains two elements `h₁,h₂`
such that `N₀ = ⟨h₁,h₂⟩` is suitable with respect to a generating set `A' ⊇ A` to
which Hull's small cancellation theorem again applies."** (tex lines 1662–1665, in
the proof of `lem:saturation`).

The printed context: `G` torsion-free and acylindrically hyperbolic, `A` Hull's
generating set, and `N` suitable with respect to `A` (the sentence before).  "Hull's
small cancellation theorem again applies" is recorded as the conclusion of
`thm:hull` (tex lines 1638–1641) at `N₀` and `A'`, for every family `g₁,…,g_m`, at
the limit-set notion. -/
def PrintedSaturationPairAndHullAgain : Prop :=
  ∀ {G : Type} [Group G], GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G →
    IsPowerTorsionFree G → ∀ (A : HullGeneratingSet G) {N : Subgroup G},
      Suitable A.alphabet N →
        ∃ A' : HullGeneratingSet G, A.alphabet.carrier ⊆ A'.alphabet.carrier ∧
          ∃ h₁ ∈ N, ∃ h₂ ∈ N,
            Suitable A'.alphabet (Subgroup.closure ({h₁, h₂} : Set G)) ∧
              ∀ {m : ℕ} (g : Fin m → G),
                ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
                  GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet Q ∧
                    (∀ i : Fin m,
                      φ (g i) ∈ (Subgroup.closure ({h₁, h₂} : Set G)).map φ) ∧
                      ∀ y : Q, IsOfFinOrder y →
                        ∃ x : G, φ x = y ∧ orderOf x = orderOf y

open TorsionFreeSectionSentencesLeastArea in
/-- **The pair `h₁, h₂` and `thm:hull` again, from the walls it uses**: the pair is
`hullSuitablePair_of_torsionFree` with `A' = A`, and `thm:hull` at the limit-set
notion comes from the least-area Greendlinger waist and the embedded bridge. -/
theorem printedSaturationPairAndHullAgain_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedSaturationPairAndHullAgain := by
  intro G _ hG htf A N hN
  haveI : IsAcylindricallyHyperbolic G :=
    HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet A
  obtain ⟨A', hA', h₁, hh₁, h₂, hh₂, hsuit, -⟩ :=
    manuscriptSentence_saturationPairAndHullAgain_of_leastAreaLeaves
      hgreendlinger hbridge htf A hN
  exact ⟨A', hA', h₁, hh₁, h₂, hh₂, hsuit, fun g =>
    TorsionFreeLimitSetEndpoints.manuscriptHullTheoremLimitSet_of_leastAreaLeaves
      hgreendlinger hbridge G hG A' hsuit g⟩

/-- **"Apply Theorem `thm:hull` to `N₀`, with respect to `A'`, with `g₁,…,g_m` a
finite generating set of `G`."** (tex lines 1665–1667, in the proof of
`lem:saturation`).

The printed context: `G` finitely presented, torsion-free and acylindrically
hyperbolic, and `N₀` suitable with respect to Hull's generating set `A'`.  The
conclusion is the quotient of `thm:hull` at the limit-set notion, together with the
kernel datum of the paragraph after `thm:hull` (tex line 1647), which the proof
uses two sentences later (tex lines 1671–1672): "finitely presented because `ker φ`
is normally generated by `m` elements". -/
def PrintedSaturationApplyHull : Prop :=
  ∀ {G : Type} [Group G] [Group.IsFinitelyPresented G],
    GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G → IsPowerTorsionFree G →
      ∀ (A' : HullGeneratingSet G) {N₀ : Subgroup G}, Suitable A'.alphabet N₀ →
        ∃ (m : ℕ) (g : Fin m → G), Subgroup.closure (Set.range g) = ⊤ ∧
          ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
            GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet Q ∧
              (∀ i : Fin m, φ (g i) ∈ N₀.map φ) ∧
                (∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y) ∧
                  ∃ T : Finset G, T.card ≤ m ∧
                    φ.ker = Subgroup.normalClosure (T : Set G)

open TorsionFreeSectionSentencesLeastArea in
/-- **The application of `thm:hull` to `N₀`, from the walls it uses**: the least-area
Greendlinger waist and the embedded bridge; the quotient's notion transfers by the
easy direction of Osin's Theorem 1.1. -/
theorem printedSaturationApplyHull_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedSaturationApplyHull := by
  intro G _ _ _hG htf A' N₀ hN₀
  haveI : IsAcylindricallyHyperbolic G :=
    HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet A'
  obtain ⟨m, g, htop, ⟨H⟩⟩ :=
    manuscriptSentence_saturationApplyHullNoOmega_of_leastAreaLeaves
      hgreendlinger hbridge htf A' hN₀
  exact ⟨m, g, htop, H.quotient.Q, H.quotient.group, H.quotient.q, H.quotient.surjective,
    @GGT.SequentialBoundary.isAcylindricallyHyperbolicLimitSet_of_isAcylindricallyHyperbolic
      H.quotient.Q H.quotient.group H.quotient.acylindricallyHyperbolic,
    H.quotient.mem_map, H.quotient.finiteOrder_lift, H.kerNormallyGenerated⟩

/-! ## The proof of `thm:torsion-free` (tex lines 1696–1716) -/

/-- **"By Lemma `lem:saturation` applied to `G₀` and `N`, there is a surjective
homomorphism `φ : G₀ → Q` with `Q` two-generated, finitely presented, torsion-free,
and acylindrically hyperbolic, and `φ(N) = Q`."** (tex lines 1698–1701, in the
proof of `thm:torsion-free`).

The printed context: `G₀` is Fournier-Facio's group, finitely presented,
torsion-free and acylindrically hyperbolic (tex lines 1675–1684), with the data
`Γ, t, J` of `PrintedFournierFacioData`, and `N` is the normal closure of
`S = tJt⁻¹` (tex line 1697). -/
def PrintedTheoremApplySaturation : Prop :=
  ∀ {G₀ : Type} [Group G₀] [Group.IsFinitelyPresented G₀],
    GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G₀ → IsPowerTorsionFree G₀ →
      ∀ F : PrintedFournierFacioData G₀,
        ∃ (Q : Type) (_ : Group Q) (φ : G₀ →* Q), Function.Surjective φ ∧
          IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
            GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet Q ∧
              (Subgroup.normalClosure (F.conjFactor : Set G₀)).map φ = ⊤

/-- **The application of `lem:saturation` to `G₀` and `N`, from the walls it uses**:
`N ≠ 1` is the sentence before (`manuscriptSentence_theoremNormalClosureNeBot`), and
`lem:saturation` at the limit-set notion comes from the least-area Greendlinger
waist, the embedded bridge, and the hard direction of Osin's Theorem 1.1, which is
proved. -/
theorem printedTheoremApplySaturation_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedTheoremApplySaturation := by
  intro G₀ _ _ hG₀ htf F
  exact TorsionFreeLimitSetEndpoints.manuscriptSaturationLimitSet_of_leastAreaLeaves
    GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet hgreendlinger hbridge
    G₀ hG₀ htf (Subgroup.normalClosure (F.conjFactor : Set G₀))
    (TorsionFreePrintedSentences.manuscriptSentence_theoremNormalClosureNeBot F).2

end TorsionFreeSectionSentencesFourLeaves
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentencesFourLeaves.printedHullProofParagraph_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentencesFourLeaves.printedSaturationPairAndHullAgain_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentencesFourLeaves.printedSaturationApplyHull_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentencesFourLeaves.printedTheoremApplySaturation_of_fourLeaves
