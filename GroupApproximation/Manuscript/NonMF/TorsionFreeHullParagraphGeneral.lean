import GroupApproximation.GGT.HullSCTheorem71GeneralLeastArea
import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# The paragraph after `thm:hull`, at every acylindrically hyperbolic group

`non_mf_groups_exist.tex`, lines 1644–1648:

> Hull's proof treats `m = 1` by passing to `G/⟨⟨r⟩⟩_G` for one element `r` and
> the general case by induction on `m`, using his clause (d), that `φ(N)` is
> again suitable [Hull, proof of Theorem 7.1], so `ker φ` is the normal closure
> of `m` elements and `Q` is finitely presented when `G` is.

`TorsionFreeSectionSentences` gives these sentences over a torsion-free ambient
group.  The paragraph, like `thm:hull`, carries no torsion hypothesis, and with
clause (d) proved over quotients with torsion
(`HullSC.normalizesNoNontrivialFinite_map_N`) the construction runs at every
ambient group:

* `manuscriptSentence_hullOneTargetOneRelatorGeneral_of_oneStep`: one target, one
  relator, and the quotient is `G/⟨⟨r⟩⟩_G`;
* `manuscriptSentence_hullInductionOnTargetsGeneral_of_oneStep`: the induction on
  `m`, clause (d) holding along it (`HullSC.hullTowerGeneral_of_oneStep`).

The kernel remark is `TorsionFreeSectionSentences.manuscriptSentence_hullKernelRemark`,
already stated for every tower.  Both sentences are given over the one-step
statement at every ambient group and over the least-area leaves.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeHullParagraphGeneral

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **"Hull's proof treats `m = 1` by passing to `G/⟨⟨r⟩⟩_G` for one element
`r` …"**, at every ambient group.  The kernel datum of the one-step construction
is a finset of at most one element; the empty case is `r = 1`. -/
theorem manuscriptSentence_hullOneTargetOneRelatorGeneral_of_oneStep
    (hOne : HullSC.HullOneStepStatementGeneral.{0})
    {G : Type} [Group G] (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) (t : G) :
    ∃ (s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) (fun _ : Fin 1 => t) 0)
      (r : G), s.step.q.ker = Subgroup.normalClosure ({r} : Set G) ∧
        Nonempty (G ⧸ Subgroup.normalClosure ({r} : Set G) ≃* s.step.Q) := by
  obtain ⟨s⟩ := hOne (k := 0) (S := fun j : Fin 0 => Fin.elim0 j) A hN
    (fun j : Fin 0 => Fin.elim0 j) t 0
  obtain ⟨T, hTcard, hTker⟩ := s.kerNormallyGenerated
  obtain ⟨x, hx⟩ := Finset.card_le_one_iff_subset_singleton.mp hTcard
  have hr : ∃ r : G,
      Subgroup.normalClosure (T : Set G) = Subgroup.normalClosure ({r} : Set G) := by
    rcases Finset.subset_singleton_iff.mp hx with rfl | rfl
    · refine ⟨1, ?_⟩
      rw [Finset.coe_empty,
        Subgroup.normalClosure_eq_bot_iff.mpr (Set.empty_subset _),
        Subgroup.normalClosure_eq_bot_iff.mpr Set.Subset.rfl]
    · exact ⟨x, by rw [Finset.coe_singleton]⟩
  obtain ⟨r, hrT⟩ := hr
  have hker : s.step.q.ker = Subgroup.normalClosure ({r} : Set G) := hTker.trans hrT
  exact ⟨s, r, hker, ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective (φ := s.step.q) s.step.surjective)⟩⟩

/-- **"… and the general case by induction on `m`, using his clause (d), that
`φ(N)` is again suitable"**, at every ambient group.  The induction is
`HullSC.hullTowerGeneral_of_oneStep`; clause (d) is the `suitable_map` field of
each step, proved over quotients with torsion. -/
theorem manuscriptSentence_hullInductionOnTargetsGeneral_of_oneStep
    (hOne : HullSC.HullOneStepStatementGeneral.{0})
    (m : ℕ) {G : Type} [Group G] (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) (t : Fin m → G) (R : ℕ) :
    ∃ s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) t R,
      Suitable s.step.hullSet.alphabet (N.map s.step.q) := by
  obtain ⟨s⟩ := HullSC.hullTowerGeneral_of_oneStep hOne m A hN
    (k := 0) (S := fun j : Fin 0 => Fin.elim0 j) (fun j : Fin 0 => Fin.elim0 j) t R
  exact ⟨s, s.step.suitable_map⟩

/-- **The one-relator sentence at every ambient group, from the least-area
leaves.** -/
theorem manuscriptSentence_hullOneTargetOneRelatorGeneral_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    {G : Type} [Group G] (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) (t : G) :
    ∃ (s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) (fun _ : Fin 1 => t) 0)
      (r : G), s.step.q.ker = Subgroup.normalClosure ({r} : Set G) ∧
        Nonempty (G ⧸ Subgroup.normalClosure ({r} : Set G) ≃* s.step.Q) :=
  manuscriptSentence_hullOneTargetOneRelatorGeneral_of_oneStep
    (HullSC.hullOneStepStatementGeneral_of_leastAreaLeaves hgreendlinger hbridge) A hN t

/-- **The induction sentence at every ambient group, from the least-area
leaves.** -/
theorem manuscriptSentence_hullInductionOnTargetsGeneral_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (m : ℕ) {G : Type} [Group G] (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) (t : Fin m → G) (R : ℕ) :
    ∃ s : HullSC.HullTower A N (fun j : Fin 0 => Fin.elim0 j) t R,
      Suitable s.step.hullSet.alphabet (N.map s.step.q) :=
  manuscriptSentence_hullInductionOnTargetsGeneral_of_oneStep
    (HullSC.hullOneStepStatementGeneral_of_leastAreaLeaves hgreendlinger hbridge) m A hN t R

end TorsionFreeHullParagraphGeneral
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeHullParagraphGeneral.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_oneStep
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeHullParagraphGeneral.manuscriptSentence_hullInductionOnTargetsGeneral_of_oneStep
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeHullParagraphGeneral.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeHullParagraphGeneral.manuscriptSentence_hullInductionOnTargetsGeneral_of_leastAreaLeaves
