import GroupApproximation.Computability.CodedProfiniteWitness
import GroupApproximation.Higman.PairedReturnProfiniteWitness
import GroupApproximation.Higman.PairedReturnCutterCode
import GroupApproximation.Higman.TransportStarCode
import GroupApproximation.Higman.TransportStarProdBotProfinite

/-!
# The coded profinite prefix of TransportStar

The effective Section 5 route begins with two exact constructions.  First,
preimage along the first projection turns a coded witness in `F₃` into its
product with the full second factor.  Second, that product is intersected with
the fixed paired-return conjugator graph.  This file identifies those two
semantic witnesses with the literal syntax emitted by `TransportStarCode`.

The fixed graph model depends only on the already isolated statement that the
literal five-generator paired-return cutter is profinitely closed.  No join or
generic image constructor is used here.
-/

namespace GroupApproximation
namespace Higman
namespace CodedTransportStarProfinite

noncomputable section

open PresentationCodes
open BenignInfCodeSemantics BenignInfCodeSubgroupSemantics
open CodedProfiniteWitness
open PairedReturnCutter PairedReturnCutterCode

abbrev P : Type := PairedReturnGraphIntersection.P

/-- The six canonical marks of `F₃ × F₃`, in the exact order used by the
paired-return and TransportStar code. -/
def pMark (i : MarkCount) : P := pGenerators.getD i 1

/-- The marks seen through the first projection: the three free generators,
then three identities. -/
def sourceMark (i : MarkCount) : Conj.F₃ := (pMark i).1

/-- Mapping a coded word-subgroup through its ambient equivalence gives the
closure of the corresponding semantic evaluations. -/
theorem map_wordSubgroup_eq_closure_eval
    {K : Type} [Group K] (c : PresentationCode) (words : List BenignInfCode.Raw)
    (e : Carrier c ≃* K) :
    (wordSubgroup c words).map e.toMonoidHom =
      Subgroup.closure {g : K | ∃ w ∈ words, e (evalWord c w) = g} := by
  unfold wordSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨evalWord c w, ⟨w, hw, rfl⟩, rfl⟩

private theorem graph_cutter_eq :
    (wordSubgroup ambientCode fiveWords).map ambientEquiv.toMonoidHom =
      fiveCutter := by
  rw [map_wordSubgroup_eq_closure_eval]
  change Subgroup.closure
    {g : Ambient | ∃ w ∈ fiveWords, PairedReturnCutterCode.evalRaw w = g} = _
  have hset :
      {g : Ambient | ∃ w ∈ fiveWords,
        PairedReturnCutterCode.evalRaw w = g} =
      {g : Ambient | g ∈
        fiveWords.map PairedReturnCutterCode.evalRaw} := by
    ext g
    simp
  rw [hset]
  exact closure_evalRaw_fiveWords

private theorem pMark_raw (i : MarkCount) :
    ambientEquiv (evalWord ambientCode (ambientPGeneratorWords.getD i [])) =
      MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (pMark i) := by
  change PairedReturnCutterCode.evalRaw
      (ambientPGeneratorWords.getD i []) =
    MatchedSubgroupAmalgam.bigInA edgeToP edgeToC (pGenerators.getD i 1)
  fin_cases i <;>
    simp [ambientPGeneratorWords, pGenerators, evalRaw_rawOf]

/-- The fixed coded paired-return graph witness.  Its only input is the exact
five-cutter closedness statement already exposed by the semantic witness. -/
def graphModel (hclosed : profiniteClosure fiveCutter = fiveCutter) :
    Model pMark Star.graphSub where
  data := PairedReturnProfiniteWitness.witness hclosed
  coded := TransportStarCode.graphSyntax
  ambientEquiv := ambientEquiv
  cutter_eq := graph_cutter_eq
  marked_eq := pMark_raw

private theorem pMark_source_raw (i : MarkCount) :
    pEquiv (evalWord pCode (pGeneratorWords.getD i [])) = pMark i := by
  change PairedReturnCutterCode.evalPRaw (pGeneratorWords.getD i []) =
    pGenerators.getD i 1
  fin_cases i <;> simp [pGeneratorWords, pGenerators, evalPRaw_pRawOf]

/-- The literal `pCode` and its six raw generator representatives model the
identity profinite overgroup of `P = F₃ × F₃`. -/
def productOvergroupModel :
    OvergroupModel pMark (ProfiniteBenignWitness.selfOvergroup (G := P)) where
  code := pCode
  marks := pGeneratorWords
  ambientEquiv := pEquiv
  marked_eq := pMark_source_raw

private theorem bot_cutter_eq :
    (wordSubgroup pCode (pGeneratorWords.take 3)).map pEquiv.toMonoidHom =
      Star.ProdBot := by
  rw [map_wordSubgroup_eq_closure_eval]
  change Subgroup.closure
      {g : P | ∃ w ∈ pGeneratorWords.take 3,
        PairedReturnCutterCode.evalPRaw w = g} = Star.ProdBot
  have hset :
      {g : P | ∃ w ∈ pGeneratorWords.take 3,
        PairedReturnCutterCode.evalPRaw w = g} =
      Set.range (MonoidHom.inl Conj.F₃ Conj.F₃ ∘
        (FreeGroup.of : Fin 3 → Conj.F₃)) := by
    ext g
    simp [pGeneratorWords, pGenerators, Function.comp_def]
    constructor
    · rintro (h | h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr hi)
  have hrange :
      Set.range (MonoidHom.inl Conj.F₃ Conj.F₃ ∘
          (FreeGroup.of : Fin 3 → Conj.F₃)) =
        (MonoidHom.inl Conj.F₃ Conj.F₃ : Conj.F₃ → P) ''
          Set.range (FreeGroup.of : Fin 3 → Conj.F₃) :=
    Set.range_comp (fun x : Conj.F₃ => MonoidHom.inl Conj.F₃ Conj.F₃ x)
      (FreeGroup.of : Fin 3 → Conj.F₃)
  rw [hset, hrange, ← MonoidHom.map_closure,
    FreeGroup.closure_range_of, Star.map_inl_top]

/-- The literal fixed `botSyntax` is the coded form of the canonical
profinite witness for `F₃ × 1`. -/
def botModel : Model pMark Star.ProdBot where
  data := Star.prodBotWitness
  coded := TransportStarCode.botSyntax
  ambientEquiv := pEquiv
  cutter_eq := bot_cutter_eq
  marked_eq := pMark_source_raw

@[simp] theorem botModel_coded :
    botModel.coded = TransportStarCode.botSyntax := rfl

/-- The first concrete TransportStar step, exactly `hprod`: preimage along
the first projection, with code produced by `BenignComapCode.transform`. -/
def hprodModel {H : Subgroup Conj.F₃} (C : Model sourceMark H) :
    Model pMark (H.comap (MonoidHom.fst Conj.F₃ Conj.F₃)) :=
  Model.comap (ProfiniteBenignWitness.selfOvergroup (G := P))
    (MonoidHom.fst Conj.F₃ Conj.F₃) productOvergroupModel C

@[simp] theorem hprodModel_coded {H : Subgroup Conj.F₃}
    (C : Model sourceMark H) :
    (hprodModel C).coded =
      BenignComapCode.transform
        (TransportStarCode.productOvergroupSyntax, C.coded) := rfl

/-- The second concrete TransportStar step, exactly `hgamma`: intersect the
fixed graph with the product witness. -/
def hgammaModel (hclosed : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H) :
    Model pMark
      (Star.graphSub ⊓ H.comap (MonoidHom.fst Conj.F₃ Conj.F₃)) :=
  Model.inf (graphModel hclosed) (hprodModel C)

@[simp] theorem hgammaModel_coded
    (hclosed : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H) :
    (hgammaModel hclosed C).coded =
      BenignInfCode.transform
        (TransportStarCode.graphSyntax,
          BenignComapCode.transform
            (TransportStarCode.productOvergroupSyntax, C.coded)) := rfl

end

end CodedTransportStarProfinite
end Higman
end GroupApproximation
