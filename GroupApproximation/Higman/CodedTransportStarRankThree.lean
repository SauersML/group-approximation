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

/-- Reinterpretation leaves the syntax untouched.  It is a transport along
`h`, so it is the identity as soon as `h` is `rfl`; the statement is needed
because the transport is an `Eq.mpr` at the whole structure, whose `.coded`
projection does not reduce on its own. -/
theorem ModelThree.subgroupCongr_coded {G : Type} [Group G]
    {mark : MarkCountThree → G} {H H' : Subgroup G}
    (h : H = H') (C : ModelThree mark H) :
    (ModelThree.subgroupCongr h C).coded = C.coded := by
  subst h
  rfl

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

/-- The rank-three skeleton names no relators.

Stated at the code's own alphabet `Fin (genCount (presentationSkeleton 2))`.
Spelling the empty set at the literal `Fin 3` instead makes the statement
type-correct only after `presentationSkeleton` is unfolded, which no tactic
working at `instances` transparency will do. -/
theorem codeRels_skeletonTwo :
    DirectProductCodeSemantics.codeRels (presentationSkeleton 2) = ∅ :=
  Finset.coe_eq_empty.mpr rfl

/-- The empty rank-three presentation is the free group on three letters. -/
def skeletonThreeEquiv : Carrier (presentationSkeleton 2) ≃* Conj.F₃ :=
  (QuotientGroup.quotientMulEquivOfEq
      (by
        show Subgroup.normalClosure
            (DirectProductCodeSemantics.codeRels (presentationSkeleton 2)) = ⊥
        rw [codeRels_skeletonTwo]
        exact le_antisymm
          (Subgroup.normalClosure_le_normal (Set.empty_subset _)) bot_le)).trans
    QuotientGroup.quotientBot

/-- Under that identification the `i`-th one-letter rank-three word is the
`i`-th free generator. -/
theorem skeletonThreeEquiv_generatorWord (i : Fin 3) :
    skeletonThreeEquiv
        (evalWord (presentationSkeleton 2) (rankThreeGeneratorWord (i : ℕ))) =
      FreeGroup.of i := by
  have hbase :
      skeletonThreeEquiv
          (evalWord (presentationSkeleton 2)
            (rankThreeGeneratorWord (i : ℕ))) =
        FreeGroup.of (letterOf (presentationSkeleton 2) (i : ℕ)) := rfl
  have hletter : letterOf (presentationSkeleton 2) (i : ℕ) = i :=
    Fin.ext (Nat.mod_eq_of_lt i.isLt)
  exact hbase.trans (congrArg FreeGroup.of hletter)

/-- The empty rank-three presentation is the coded identity overgroup. -/
def rankThreeOvergroupModel :
    OvergroupModelThree (FreeGroup.of : Fin 3 → Conj.F₃)
      (ProfiniteBenignWitness.selfOvergroup (G := Conj.F₃)) where
  code := presentationSkeleton 2
  marks := (rankThreeGeneratorWord 0,
    rankThreeGeneratorWord 1, rankThreeGeneratorWord 2)
  ambientEquiv := skeletonThreeEquiv
  marked_eq := by
    refine ⟨?_, ?_, ?_⟩
    · exact skeletonThreeEquiv_generatorWord 0
    · exact skeletonThreeEquiv_generatorWord 1
    · exact skeletonThreeEquiv_generatorWord 2

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

/-- The three-mark syntax emitted by the final split preimage, as a function
of the join syntax alone.

Isolating it as a plain function is what makes the identification below
provable: the model term itself is type-correct only at default transparency
(its `ambientEquiv` field's type mentions `(hjoinSyntax hfive C).1`), so no
`rw` motive over it can be checked, whereas `congrArg` on this function is
non-dependent. -/
def codedOfJoinSyntax (w : BenignInfCode.WitnessSyntax) : RankThreeInputData :=
  let out :=
    BenignComapThreeCode.transform
      ((presentationSkeleton 2,
          ([], [rankThreeGeneratorWord 0, rankThreeGeneratorWord 1,
            rankThreeGeneratorWord 2])),
        (w.1, (w.2.1,
          [w.2.2.getD 3 [], w.2.2.getD 4 [], w.2.2.getD 5 []])))
  (out.1, (out.2.1,
    (out.2.2.getD 0 [], out.2.2.getD 1 [], out.2.2.getD 2 [])))

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
  have h0 : (transportStarModel hfive T C hclosed).coded =
      (ModelThree.comap
        (ProfiniteBenignWitness.selfOvergroup (G := Conj.F₃))
        (MonoidHom.inr Conj.F₃ Conj.F₃)
        rankThreeOvergroupModel
        (finalRightModel hfive T C hclosed)).coded :=
    ModelThree.subgroupCongr_coded (final_comap_eq T) _
  have h1 : (ModelThree.comap
      (ProfiniteBenignWitness.selfOvergroup (G := Conj.F₃))
      (MonoidHom.inr Conj.F₃ Conj.F₃)
      rankThreeOvergroupModel
      (finalRightModel hfive T C hclosed)).coded =
      codedOfJoinSyntax (hjoinSyntax hfive C) := rfl
  have h2 : codedOfJoinSyntax (TransportStarCode.hjoin x) =
      TransportStarCode.rankThreeData x := rfl
  exact h0.trans (h1.trans ((congrArg codedOfJoinSyntax hj).trans h2))

end

end CodedTransportStarRankThree
end Higman
end GroupApproximation
