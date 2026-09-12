import GroupApproximation.GGT.AcylindricallyHyperbolicOsin
import GroupApproximation.Manuscript.NonMF.TorsionFreeLeastAreaAssembly
import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:torsion-free` at the printed notion of acylindrical hyperbolicity

The manuscript's *acylindrically hyperbolic* is Osin's notion,
`GGT.IsAcylindricallyHyperbolicOsin`; the section's landed statements carry Hull's
Cayley-graph form `TorsionFree.IsAcylindricallyHyperbolic`.  This module restates
the printed endpoints of `sec:torsion-free` at Osin's notion and derives each from
the landed form through `GGT.isAcylindricallyHyperbolic_iff_osin`:

* `thm:torsion-free` — `PrintedTorsionFreeTheoremOsin`;
* `thm:hull` — `PrintedHullSmallCancellationOsin`, with Hull's generating set
  supplied by `GGT.exists_hullGeneratingSet_of_osin`;
* `lem:saturation` — `PrintedSaturationOsin`;
* `cor:regular-nonmf-algebra` — `PrintedRegularNonMFAlgebraOsin`.

Non-elementarity is spelled as two independent loxodromic elements; the
limit-set spelling is the subject of `GGT.SequentialBoundary`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeOsinNotion

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.ReducedGroupCStarTrace
open GroupApproximation.GroupVonNeumann

/-! ## `thm:torsion-free` -/

/-- **`thm:torsion-free`, as printed, at Osin's notion** (tex line 284). -/
def PrintedTorsionFreeTheoremOsin : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
      GGT.IsAcylindricallyHyperbolicOsin Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
        (∀ (M : Type) (_ : Group M), IsOperatorMF M →
          ∀ (f : Q →* M) (x : Q), f x = 1) ∧
        (∀ (L : Type) (_ : Group L) (r : Q →* L), Function.Surjective r →
          Nontrivial L → ¬ IsOperatorMF L)

/-- The landed printed theorem gives it: only the acylindrical-hyperbolicity
clause changes, through `GGT.isAcylindricallyHyperbolic_iff_osin`. -/
theorem printedTorsionFreeTheoremOsin_of_printed (h : PrintedTorsionFreeTheorem) :
    PrintedTorsionFreeTheoremOsin := by
  obtain ⟨Q, instQ, hgen, hfp, htf, hah, hrest⟩ := h
  letI := instQ
  exact ⟨Q, instQ, hgen, hfp, htf, (GGT.isAcylindricallyHyperbolic_iff_osin Q).mp hah,
    hrest⟩

/-- **`thm:torsion-free` at Osin's notion**, from the Fournier-Facio paragraph and
the two Hull leaves. -/
theorem manuscriptTorsionFreeTheoremOsin_of_leastAreaLeaves
    (hFFF : FournierFacioParagraph)
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedTorsionFreeTheoremOsin :=
  printedTorsionFreeTheoremOsin_of_printed
    (TorsionFreeLeastAreaAssembly.manuscriptTorsionFreeTheorem_of_leastAreaLeaves
      hFFF hgreendlinger hbridge)

/-! ## `thm:hull` -/

/-- **`thm:hull`, as printed, at Osin's notion** (tex line 1636): for every group
acylindrically hyperbolic in Osin's sense, Hull's generating set `A`, a suitable
`N`, and `g₁, …, g_m`, there is a surjection onto a group acylindrically hyperbolic
in Osin's sense with `φ(gᵢ) ∈ φ(N)`, lifting elements of finite order with their
order. -/
def PrintedHullSmallCancellationOsin : Prop :=
  ∀ (G : Type) [Group G], GGT.IsAcylindricallyHyperbolicOsin G →
    ∀ (A : HullGeneratingSet G) {N : Subgroup G}, Suitable A.alphabet N →
      ∀ {m : ℕ} (g : Fin m → G),
        ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
          GGT.IsAcylindricallyHyperbolicOsin Q ∧ (∀ i : Fin m, φ (g i) ∈ N.map φ) ∧
            ∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y

/-- The printed statement at the Cayley-graph notion gives it. -/
theorem printedHullSmallCancellationOsin_of_current
    (h : TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0}) :
    PrintedHullSmallCancellationOsin := by
  intro G _ hG A N hN m g
  haveI : IsAcylindricallyHyperbolic G := GGT.isAcylindricallyHyperbolic_of_osin hG
  obtain ⟨H⟩ := h A hN g
  exact ⟨H.Q, H.group, H.q, H.surjective,
    @GGT.osin_of_isAcylindricallyHyperbolic H.Q H.group H.acylindricallyHyperbolic,
    H.mem_map, H.finiteOrder_lift⟩

/-- **`thm:hull` at Osin's notion over a torsion-free ambient group**, from the
two Hull leaves. -/
theorem manuscriptSentence_hullTheoremTorsionFreeOsin_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    ∀ (G : Type) [Group G], GGT.IsAcylindricallyHyperbolicOsin G →
      IsPowerTorsionFree G →
        ∀ (A : HullGeneratingSet G) {N : Subgroup G}, Suitable A.alphabet N →
          ∀ {m : ℕ} (g : Fin m → G),
            ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
              GGT.IsAcylindricallyHyperbolicOsin Q ∧ (∀ i : Fin m, φ (g i) ∈ N.map φ) ∧
                ∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y := by
  intro G _ hG htf A N hN m g
  haveI : IsAcylindricallyHyperbolic G := GGT.isAcylindricallyHyperbolic_of_osin hG
  obtain ⟨H⟩ :=
    TorsionFreeLeastAreaAssembly.hullSmallCancellationTorsionFreePrinted_of_leastAreaLeaves
      hgreendlinger hbridge htf A hN g
  exact ⟨H.quotient.Q, H.quotient.group, H.quotient.q, H.quotient.surjective,
    @GGT.osin_of_isAcylindricallyHyperbolic H.quotient.Q H.quotient.group
      H.quotient.acylindricallyHyperbolic,
    H.quotient.mem_map, H.quotient.finiteOrder_lift⟩

/-- **Hull's generating set for the section's groups** (tex line 1629), at Osin's
notion. -/
theorem manuscriptSentence_hullGeneratingSetOsin (G : Type) [Group G]
    (hG : GGT.IsAcylindricallyHyperbolicOsin G) : Nonempty (HullGeneratingSet G) :=
  GGT.exists_hullGeneratingSet_of_osin G hG

/-! ## `lem:saturation` -/

/-- **`lem:saturation`, as printed, at Osin's notion** (tex line 1650). -/
def PrintedSaturationOsin : Prop :=
  ∀ (G : Type) [Group G] [Group.IsFinitelyPresented G],
    GGT.IsAcylindricallyHyperbolicOsin G → IsPowerTorsionFree G →
      ∀ (N : Subgroup G) [N.Normal], N ≠ ⊥ →
        ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
          IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
            GGT.IsAcylindricallyHyperbolicOsin Q ∧ N.map φ = ⊤

/-- The printed lemma at the Cayley-graph notion gives it. -/
theorem printedSaturationOsin_of_noOmega (h : PrintedSaturationNoOmega.{0}) :
    PrintedSaturationOsin := by
  intro G _ _ hG htf N _ hN
  haveI : IsAcylindricallyHyperbolic G := GGT.isAcylindricallyHyperbolic_of_osin hG
  obtain ⟨S⟩ := h G htf N hN
  exact ⟨S.Q, S.group, S.q, S.surjective, ⟨S.generatorOne, S.generatorTwo, S.twoGenerated⟩,
    S.finitelyPresented, S.torsionFree,
    @GGT.osin_of_isAcylindricallyHyperbolic S.Q S.group S.acylindricallyHyperbolic,
    S.map_eq_top⟩

/-- **`lem:saturation` at Osin's notion**, from the two Hull leaves. -/
theorem manuscriptSaturationOsin_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedSaturationOsin :=
  printedSaturationOsin_of_noOmega
    (TorsionFreeLeastAreaAssembly.printedSaturationNoOmega_of_leastAreaLeaves
      hgreendlinger hbridge)

/-! ## `cor:regular-nonmf-algebra` -/

/-- **`cor:regular-nonmf-algebra`, as printed, at Osin's notion** (tex line 1718);
the group clause records the properties the printed proof uses, at the printed
notion of acylindrical hyperbolicity. -/
def PrintedRegularNonMFAlgebraOsin : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    Countable Q ∧ IsPowerTorsionFree Q ∧ GGT.IsAcylindricallyHyperbolicOsin Q ∧
      IsTwoGenerated Q ∧
        TopologicalSpace.SeparableSpace (ReducedGroupCStar Q) ∧
          (1 : ReducedGroupCStar Q) ≠ 0 ∧
            (∃ g₁ g₂ : Q, Subgroup.closure ({g₁, g₂} : Set Q) = ⊤ ∧
              leftRegularOperator Q g₁ ∈
                  unitary (GroupHilbert Q →L[ℂ] GroupHilbert Q) ∧
                leftRegularOperator Q g₂ ∈
                  unitary (GroupHilbert Q →L[ℂ] GroupHilbert Q) ∧
                  (StarAlgebra.adjoin ℂ
                    ({leftRegularOperator Q g₁, leftRegularOperator Q g₂} :
                      Set (GroupHilbert Q →L[ℂ] GroupHilbert Q))).topologicalClosure
                    = reducedGroupCStarSubalgebra Q) ∧
              IsSimpleCStar (ReducedGroupCStar Q) ∧
                HasUniqueTracialState (ReducedGroupCStar Q) ∧
                  IsStableRankOne (ReducedGroupCStar Q) ∧
                    IsStablyFiniteCStarAlgebra (ReducedGroupCStar Q) ∧
                      ¬ IsMFAlgebra (ReducedGroupCStar Q)

/-- The landed printed corollary gives it. -/
theorem printedRegularNonMFAlgebraOsin_of_printed (h : PrintedRegularNonMFAlgebra) :
    PrintedRegularNonMFAlgebraOsin := by
  obtain ⟨Q, instQ, hc, htf, hah, hrest⟩ := h
  letI := instQ
  exact ⟨Q, instQ, hc, htf, (GGT.isAcylindricallyHyperbolic_iff_osin Q).mp hah, hrest⟩

/-- **`cor:regular-nonmf-algebra` at Osin's notion**, from the Fournier-Facio
paragraph, the two Hull leaves, Dahmani–Guirardel–Osin 2.35 at its source
hypothesis and Gerasimova–Osin 1.1. -/
theorem manuscriptRegularNonMFAlgebraOsin_of_leastAreaLeaves
    (hFFF : FournierFacioParagraph)
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hDGO : SimpleUniqueTraceAtHypEmbedded)
    (hGO : GerasimovaOsinTheorem11Printed) : PrintedRegularNonMFAlgebraOsin :=
  printedRegularNonMFAlgebraOsin_of_printed
    (TorsionFreeLeastAreaAssembly.manuscriptRegularNonMFAlgebra_of_leastAreaLeaves
      hFFF hgreendlinger hbridge hDGO hGO)

end TorsionFreeOsinNotion
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion.printedTorsionFreeTheoremOsin_of_printed
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion.manuscriptTorsionFreeTheoremOsin_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion.printedHullSmallCancellationOsin_of_current
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion.manuscriptSentence_hullTheoremTorsionFreeOsin_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion.manuscriptSentence_hullGeneratingSetOsin
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion.printedSaturationOsin_of_noOmega
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion.manuscriptSaturationOsin_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion.printedRegularNonMFAlgebraOsin_of_printed
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion.manuscriptRegularNonMFAlgebraOsin_of_leastAreaLeaves
