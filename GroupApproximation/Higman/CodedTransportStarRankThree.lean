import GroupApproximation.Computability.CodedProfiniteWitnessThree
import GroupApproximation.Higman.BridgePresentation
import GroupApproximation.Higman.CodedTransportStarProfinite
import GroupApproximation.Higman.TransportStarCodeSemantics

/-!
# The concrete TransportStar rank-three handoff

This module turns the six-mark special join model into the literal three-mark
split preimage emitted by `TransportStarCode.rankThreeData`.  The only
remaining semantic input is the special join cutter closedness used to build
the six-mark model itself.
-/

namespace GroupApproximation
namespace Higman
namespace CodedTransportStarRankThree

noncomputable section

open PresentationCodes
open BenignInfCodeSemantics
open CodedProfiniteWitness
open CodedTransportStarProfinite
open PairedReturnCutter PairedReturnCutterCode
open TransportStarCode MikhailovaRopeCode

abbrev P : Type := PairedReturnGraphIntersection.P

/-- The semantic subgroup immediately before the final split preimage. -/
abbrev joinOutput (T : Set ↑Conj.K) : Subgroup P :=
  (Star.graphSub ⊓
      ((Star.coordSub T).map Conj.cbHom).comap
        (MonoidHom.fst Conj.F₃ Conj.F₃)) ⊔ Star.ProdBot

/-- Reinterpret a three-mark model along an equality of its source subgroup. -/
def ModelThree.subgroupCongr {G : Type} [Group G]
    {mark : MarkCountThree → G} {H H' : Subgroup G}
    (h : H = H') (C : ModelThree mark H) : ModelThree mark H' := by
  rw [← h]
  exact C

/-- The last three join marks, with the unchanged join ambient and cutter. -/
def finalRightModel
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    (T : Set ↑Conj.K)
    (C : Model sourceMark ((Star.coordSub T).map Conj.cbHom))
    (hclosed : SpecialJoinClosedObligation hfive C) :
    ModelThree
      (fun i : Fin 3 ↦ MonoidHom.inr Conj.F₃ Conj.F₃ (FreeGroup.of i))
      (joinOutput T) := by
  let J := hjoinModelOfClosed hfive C hclosed
  let s := hjoinSyntax hfive C
  refine
    { data := J.data
      coded := (s.1, (s.2.1,
        (s.2.2.getD 3 [], s.2.2.getD 4 [], s.2.2.getD 5 [])))
      ambientEquiv := J.ambientEquiv
      cutter_eq := J.cutter_eq
      marked_eq := ?_ }
  have hmark := J.marked_eq
  refine ⟨?_, ?_, ?_⟩
  · change J.ambientEquiv (evalWord s.1 (s.2.2.getD 3 [])) =
      J.data.witness.emb (pMark 3)
    exact hmark (3 : Fin 6)
  · change J.ambientEquiv (evalWord s.1 (s.2.2.getD 4 [])) =
      J.data.witness.emb (pMark 4)
    exact hmark (4 : Fin 6)
  · change J.ambientEquiv (evalWord s.1 (s.2.2.getD 5 [])) =
      J.data.witness.emb (pMark 5)
    exact hmark (5 : Fin 6)

/-- The empty rank-three presentation is the coded identity overgroup. -/
def rankThreeOvergroupModel :
    OvergroupModelThree (FreeGroup.of : Fin 3 → Conj.F₃)
      (ProfiniteBenignWitness.selfOvergroup (G := Conj.F₃)) where
  code := presentationSkeleton 2
  marks := (rankThreeGeneratorWord 0,
    rankThreeGeneratorWord 1, rankThreeGeneratorWord 2)
  ambientEquiv := by
    change PresentedGroup
      (DirectProductCodeSemantics.codeRels (presentationSkeleton 2)) ≃*
        Conj.F₃
    have hset :
        DirectProductCodeSemantics.codeRels (presentationSkeleton 2) =
          (∅ : Set (FreeGroup (Fin 3))) := by
      ext w
      change w ∈ (↑(∅ : Finset (FreeGroup (Fin 3))) :
          Set (FreeGroup (Fin 3))) ↔ w ∈ (∅ : Set (FreeGroup (Fin 3)))
      constructor
      · exact fun hw ↦ (Finset.not_mem_empty w hw).elim
      · exact fun hw ↦ (Set.not_mem_empty w hw).elim
    exact
      (QuotientGroup.quotientMulEquivOfEq
        (congrArg Subgroup.normalClosure hset)).trans
          (BridgePresentation.freePresentedEquiv (Fin 3))
  marked_eq := by
    refine ⟨?_, ?_, ?_⟩ <;>
      rw [BenignComapCodeSemantics.evalWord_generatorWord,
        BridgePresentation.freePresentedEquiv_of]

/-- The exact semantic equality read by the final split preimage. -/
theorem final_comap_eq (T : Set ↑Conj.K) :
    (joinOutput T).comap (MonoidHom.inr Conj.F₃ Conj.F₃) =
      (Star.coordSub T).map Star.evalHom := by
  unfold joinOutput
  rw [Star.special_sup_eq, Star.comap_inr_prod_top]

/-- The concrete three-mark strengthened model emitted by TransportStar. -/
def transportStarModel
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    (T : Set ↑Conj.K)
    (C : Model sourceMark ((Star.coordSub T).map Conj.cbHom))
    (hclosed : SpecialJoinClosedObligation hfive C) :
    ModelThree (FreeGroup.of : Fin 3 → Conj.F₃)
      ((Star.coordSub T).map Star.evalHom) :=
  ModelThree.subgroupCongr (final_comap_eq T)
    (ModelThree.comap
      (ProfiniteBenignWitness.selfOvergroup (G := Conj.F₃))
      (MonoidHom.inr Conj.F₃ Conj.F₃)
      rankThreeOvergroupModel (finalRightModel hfive T C hclosed))

/-- When the varying model has the literal TransportStar input syntax, the
three-mark model is definitionally the existing `rankThreeData`. -/
theorem transportStarModel_coded
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    (T : Set ↑Conj.K)
    (C : Model sourceMark ((Star.coordSub T).map Conj.cbHom))
    (hclosed : SpecialJoinClosedObligation hfive C)
    (x : TransportStarCode.Input)
    (hC : C.coded = TransportStarCode.varyingProductSyntax x) :
    (transportStarModel hfive T C hclosed).coded =
      TransportStarCode.rankThreeData x := by
  have hj := hjoinSyntax_eq_transportStar hfive C x hC
  unfold transportStarModel ModelThree.subgroupCongr ModelThree.comap
    finalRightModel rankThreeOvergroupModel
  simp only
  rw [hj]
  rfl

end

end CodedTransportStarRankThree
end Higman
end GroupApproximation
