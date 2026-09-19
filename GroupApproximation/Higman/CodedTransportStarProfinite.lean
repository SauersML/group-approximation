import GroupApproximation.Computability.CodedProfiniteWitness
import GroupApproximation.Computability.BenignSupCodeModelSemantics
import GroupApproximation.Higman.PairedReturnProfiniteWitness
import GroupApproximation.Higman.PairedReturnCutterCode
import GroupApproximation.Higman.TransportStarCode
import GroupApproximation.Higman.TransportStarProdBotProfinite
import GroupApproximation.Higman.ProfiniteBenignProductSeparable
import GroupApproximation.Higman.ProfiniteBenignFactorizationReflection
import GroupApproximation.Higman.TransportStarSourceProductSeparable

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

/-- The six canonical marks generate the whole source double. -/
theorem pMark_closure_top :
    Subgroup.closure (Set.range pMark) = (⊤ : Subgroup P) := by
  apply top_unique
  rintro ⟨x, y⟩ -
  have hleft : (x, 1) ∈ Subgroup.closure (Set.range pMark) := by
    have hx : x ∈ Subgroup.closure
        (Set.range (FreeGroup.of : Fin 3 → Conj.F₃)) := by
      rw [FreeGroup.closure_range_of]
      exact Subgroup.mem_top x
    refine Subgroup.closure_induction
      (p := fun z _ ↦ (z, 1) ∈ Subgroup.closure (Set.range pMark))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Subgroup.subset_closure ⟨⟨0, by omega⟩, by rfl⟩
      · exact Subgroup.subset_closure ⟨⟨1, by omega⟩, by rfl⟩
      · exact Subgroup.subset_closure ⟨⟨2, by omega⟩, by rfl⟩
    · exact Subgroup.one_mem _
    · intro a b _ _ ha hb
      simpa using Subgroup.mul_mem _ ha hb
    · intro a _ ha
      simpa using Subgroup.inv_mem _ ha
  have hright : (1, y) ∈ Subgroup.closure (Set.range pMark) := by
    have hy : y ∈ Subgroup.closure
        (Set.range (FreeGroup.of : Fin 3 → Conj.F₃)) := by
      rw [FreeGroup.closure_range_of]
      exact Subgroup.mem_top y
    refine Subgroup.closure_induction
      (p := fun z _ ↦ (1, z) ∈ Subgroup.closure (Set.range pMark))
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Subgroup.subset_closure ⟨⟨3, by omega⟩, by rfl⟩
      · exact Subgroup.subset_closure ⟨⟨4, by omega⟩, by rfl⟩
      · exact Subgroup.subset_closure ⟨⟨5, by omega⟩, by rfl⟩
    · exact Subgroup.one_mem _
    · intro a b _ _ ha hb
      simpa using Subgroup.mul_mem _ ha hb
    · intro a _ ha
      simpa using Subgroup.inv_mem _ ha
  simpa using Subgroup.mul_mem _ hleft hright

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

/-- The fixed graph model reflects every prescribed quotient; this is the
exact paired-return theorem, not an additional compiler input. -/
theorem graphModel_factorizationReflecting
    (hclosed : profiniteClosure fiveCutter = fiveCutter) :
    (graphModel hclosed).data.FactorizationReflecting :=
  PairedReturnProfiniteWitness.witness_factorizationReflecting hclosed

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

/-- The product-separation invariant passes through the actual `hprod`
preimage because first projection is surjective. -/
theorem hprodModel_productSeparable {H : Subgroup Conj.F₃}
    (C : Model sourceMark H) (hC : C.data.ProductSeparable) :
    (hprodModel C).data.ProductSeparable := by
  exact ProfiniteBenignWitness.ProductSeparable.comap_of_surjective
    C.data hC (ProfiniteBenignWitness.selfOvergroup (G := P))
      (MonoidHom.fst Conj.F₃ Conj.F₃) Prod.fst_surjective

/-- Prescribed quotients of the varying first coordinate are reflected by a
finite quotient of the literal hprod ambient. -/
theorem hprodModel_factorizationReflecting_fst
    {H : Subgroup Conj.F₃} (C : Model sourceMark H)
    (hC : C.data.FactorizationReflecting)
    (Q : Type) [Group Q] [Finite Q] (q : Conj.F₃ →* Q) :
    ∃ (R : Type) (_ : Group R) (_ : Finite R)
        (p : (hprodModel C).data.witness.K →* R),
      ∀ g : P,
        p ((hprodModel C).data.witness.emb g) ∈
            (hprodModel C).data.witness.L.map p →
          q g.1 ∈ H.map q := by
  exact ProfiniteBenignWitness.FactorizationReflecting.comap_coordinate
    C.data hC (ProfiniteBenignWitness.selfOvergroup (G := P))
      (MonoidHom.fst Conj.F₃ Conj.F₃) Q q

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

/-- Product separation through the actual graph/hprod Inf.  Synchronization
uses the concrete `retK ∘ fst` detector, so the hprod side needs only the
valid coordinate reflection inherited from `C`. -/
theorem hgammaModel_productSeparable
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (hH : H ≤ Conj.cbHom.range)
    (C : Model sourceMark H)
    (hGraphProduct : (graphModel hfive).data.ProductSeparable)
    (hCProduct : C.data.ProductSeparable)
    (hCReflect : C.data.FactorizationReflecting) :
    (hgammaModel hfive C).data.ProductSeparable := by
  exact ProfiniteBenignWitness.ProductSeparable.inf
    (graphModel hfive).data (hprodModel C).data hGraphProduct
      (hprodModel_productSeparable C hCProduct)
      (TransportStarSourceProductSeparable.graph_fstComap_infSynchronizing
        H hH (graphModel hfive).data
          (graphModel_factorizationReflecting hfive) C.data hCReflect)

/-- Literal coordinate-subgroup specialization used by TransportStar. -/
theorem hgammaModel_coord_productSeparable
    (hfive : profiniteClosure fiveCutter = fiveCutter) (T : Set ↑Conj.K)
    (C : Model sourceMark ((Star.coordSub T).map Conj.cbHom))
    (hGraphProduct : (graphModel hfive).data.ProductSeparable)
    (hCProduct : C.data.ProductSeparable)
    (hCReflect : C.data.FactorizationReflecting) :
    (hgammaModel hfive C).data.ProductSeparable := by
  apply hgammaModel_productSeparable hfive
  · rintro _ ⟨w, -, rfl⟩
    exact ⟨w, rfl⟩
  · exact hGraphProduct
  · exact hCProduct
  · exact hCReflect

@[simp] theorem hgammaModel_coded
    (hclosed : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H) :
    (hgammaModel hclosed C).coded =
      BenignInfCode.transform
        (TransportStarCode.graphSyntax,
          BenignComapCode.transform
            (TransportStarCode.productOvergroupSyntax, C.coded)) := rfl

/-! ## The exact special-Sup boundary -/

/-- Closedness of the one literal two-HNN cutter used by TransportStar.  This
is intentionally specialized to the graph/product intersection on the left
and the fixed split first factor on the right. -/
def SpecialJoinClosedObligation
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H) : Prop :=
  ProfiniteBenignJoin.CutterClosedObligation
    (hgammaModel hfive C).data botModel.data

/-- The strengthened semantic join witness once its special cutter is known
closed. -/
def hjoinData
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H)
    (hclosed : SpecialJoinClosedObligation hfive C) :
    ProfiniteBenignWitness
      ((Star.graphSub ⊓ H.comap (MonoidHom.fst Conj.F₃ Conj.F₃)) ⊔
        Star.ProdBot) :=
  ProfiniteBenignJoin.witness (hgammaModel hfive C).data botModel.data hclosed

/-- The literal Sup syntax at the graph/product stage. -/
def hjoinSyntax
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H) :
    BenignInfCode.WitnessSyntax :=
  BenignSupCode.transform ((hgammaModel hfive C).coded, botModel.coded)

/-- When the input model carries the padded syntax built from an original
rank-three datum, this stage is definitionally the existing
`TransportStarCode.hjoin`. -/
theorem hjoinSyntax_eq_transportStar
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H)
    (x : TransportStarCode.Input)
    (hC : C.coded = TransportStarCode.varyingProductSyntax x) :
    hjoinSyntax hfive C = TransportStarCode.hjoin x := by
  unfold hjoinSyntax
  rw [hgammaModel_coded, hC]
  rfl

/-- The exact code-semantic facts still needed to identify the emitted
`BenignSupCode` syntax with the special semantic join witness.  Existing
The ambient equivalence and all six mark identifications are supplied
unconditionally by `Model.supLevel2Equiv` and
`Model.supLevel2Equiv_outputMark`.  This single field is precisely the
remaining final-cutter identification at the actual TransportStar inputs. -/
structure SpecialJoinCodeSemantics
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H)
    (hclosed : SpecialJoinClosedObligation hfive C) where
  cutter_eq :
    (wordSubgroup (hjoinSyntax hfive C).1
        (hjoinSyntax hfive C).2.1).map
        (Model.supLevel2Equiv (hgammaModel hfive C) botModel).toMonoidHom =
      (hjoinData hfive C hclosed).witness.L

private theorem diagonal_mem (x : BenignSupCode.Input) (i : MarkCount) :
    BenignInfCode.diagonalAt x i ∈ BenignInfCode.diagonalMarks x := by
  fin_cases i <;> simp [BenignInfCode.diagonalMarks]

private theorem exists_diagonalAt_of_mem {x : BenignSupCode.Input}
    {raw : BenignSupCode.Raw} (hraw : raw ∈ BenignInfCode.diagonalMarks x) :
    ∃ i : MarkCount, raw = BenignInfCode.diagonalAt x i := by
  simp only [BenignInfCode.diagonalMarks, List.mem_cons] at hraw
  rcases hraw with h | h | h | h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩
  · exact ⟨5, h.resolve_right (by simp)⟩

/-- The emitted two-family cutter is exactly Higman's semantic `joinL` for
the actual six-generator TransportStar source. -/
theorem hjoin_cutter_eq
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H) :
    (wordSubgroup (hjoinSyntax hfive C).1
        (hjoinSyntax hfive C).2.1).map
        (Model.supLevel2Equiv (hgammaModel hfive C) botModel).toMonoidHom =
      Higman.joinL (hgammaModel hfive C).data.witness
        botModel.data.witness := by
  let C₁ := hgammaModel hfive C
  let C₂ := botModel
  let x := Model.supInput C₁ C₂
  let e := Model.supLevel2Equiv C₁ C₂
  let S : Subgroup (Higman.JoinLevel2 C₁.data.witness C₂.data.witness) :=
    (wordSubgroup (BenignSupCode.level2 x)
      (BenignSupCode.firstConjugates x ++
        BenignSupCode.secondConjugates x)).map e.toMonoidHom
  change S = Higman.joinL C₁.data.witness C₂.data.witness
  apply le_antisymm
  · rintro z ⟨y, hy, rfl⟩
    refine Subgroup.closure_induction
      (p := fun y _ ↦ e y ∈ Higman.joinL C₁.data.witness C₂.data.witness)
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨raw, hraw, rfl⟩
      rcases List.mem_append.mp hraw with hraw | hraw
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hraw
        obtain ⟨i, rfl⟩ := exists_diagonalAt_of_mem hd
        rw [Model.supLevel2Equiv_firstConjugate,
          Model.supBaseEquiv_diagonalAt]
        refine Subgroup.mem_sup_left ⟨Higman.joinEmb₂ C₁.data.witness
          C₂.data.witness (pMark i), ⟨pMark i, Subgroup.mem_top _, rfl⟩, ?_⟩
        simp [Higman.joinEmb₂]
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hraw
        obtain ⟨i, rfl⟩ := exists_diagonalAt_of_mem hd
        rw [Model.supLevel2Equiv_secondConjugate,
          Model.supBaseEquiv_diagonalAt]
        refine Subgroup.mem_sup_right ⟨Higman.joinEmb₂ C₁.data.witness
          C₂.data.witness (pMark i), ⟨pMark i, Subgroup.mem_top _, rfl⟩, ?_⟩
        simp [Higman.joinEmb₂]
    · simp
    · intro a b _ _ ha hb
      simpa using Subgroup.mul_mem _ ha hb
    · intro a _ ha
      simpa using Subgroup.inv_mem _ ha
  · apply sup_le
    · rintro _ ⟨z, ⟨g, -, rfl⟩, rfl⟩
      let f₁ : P →* Higman.JoinLevel2 C₁.data.witness C₂.data.witness :=
        (MulAut.conj
          ((HNNExtension.of : Higman.JoinLevel1 C₁.data.witness
            C₂.data.witness →* Higman.JoinLevel2 C₁.data.witness
              C₂.data.witness) HNNExtension.t)⁻¹).toMonoidHom.comp
          (Higman.joinEmb₂ C₁.data.witness C₂.data.witness)
      change f₁ g ∈ S
      have hg : g ∈ Subgroup.closure (Set.range pMark) := by
        rw [pMark_closure_top]
        exact Subgroup.mem_top g
      refine Subgroup.closure_induction
        (p := fun g _ ↦ f₁ g ∈ S)
        ?_ ?_ ?_ ?_ hg
      · rintro _ ⟨i, rfl⟩
        refine ⟨evalWord (BenignSupCode.level2 x)
          (BenignSupCode.liftToLevel2 x
            (MikhailovaRopeCode.firstStableConjugate
              (BenignSupCode.productBase x)
              (BenignInfCode.diagonalAt x i))), ?_, ?_⟩
        · exact evalWord_mem_wordSubgroup _ _
            (List.mem_append_left _ (List.mem_map.mpr
              ⟨_, diagonal_mem x i, rfl⟩))
        · change Model.supLevel2Equiv C₁ C₂
              (evalWord (BenignSupCode.level2 (Model.supInput C₁ C₂))
                (BenignSupCode.liftToLevel2 (Model.supInput C₁ C₂)
                  (MikhailovaRopeCode.firstStableConjugate
                    (BenignSupCode.productBase (Model.supInput C₁ C₂))
                    (BenignInfCode.diagonalAt (Model.supInput C₁ C₂) i)))) =
              f₁ (pMark i)
          rw [Model.supLevel2Equiv_firstConjugate,
            Model.supBaseEquiv_diagonalAt]
          simp [f₁, Higman.joinEmb₂]
      · simp
      · intro a b _ _ ha hb
        simpa using Subgroup.mul_mem _ ha hb
      · intro a _ ha
        simpa using Subgroup.inv_mem _ ha
    · rintro _ ⟨z, ⟨g, -, rfl⟩, rfl⟩
      let f₂ : P →* Higman.JoinLevel2 C₁.data.witness C₂.data.witness :=
        (MulAut.conj
          (HNNExtension.t : Higman.JoinLevel2 C₁.data.witness
            C₂.data.witness)⁻¹).toMonoidHom.comp
          (Higman.joinEmb₂ C₁.data.witness C₂.data.witness)
      change f₂ g ∈ S
      have hg : g ∈ Subgroup.closure (Set.range pMark) := by
        rw [pMark_closure_top]
        exact Subgroup.mem_top g
      refine Subgroup.closure_induction
        (p := fun g _ ↦ f₂ g ∈ S)
        ?_ ?_ ?_ ?_ hg
      · rintro _ ⟨i, rfl⟩
        refine ⟨evalWord (BenignSupCode.level2 x)
          (MikhailovaRopeCode.firstStableConjugate
            (BenignSupCode.level1 x)
            (BenignSupCode.liftToLevel1 x
              (BenignInfCode.diagonalAt x i))), ?_, ?_⟩
        · exact evalWord_mem_wordSubgroup _ _
            (List.mem_append_right _ (List.mem_map.mpr
              ⟨_, diagonal_mem x i, rfl⟩))
        · change Model.supLevel2Equiv C₁ C₂
              (evalWord (BenignSupCode.level2 (Model.supInput C₁ C₂))
                (MikhailovaRopeCode.firstStableConjugate
                  (BenignSupCode.level1 (Model.supInput C₁ C₂))
                  (BenignSupCode.liftToLevel1 (Model.supInput C₁ C₂)
                    (BenignInfCode.diagonalAt (Model.supInput C₁ C₂) i)))) =
              f₂ (pMark i)
          rw [Model.supLevel2Equiv_secondConjugate,
            Model.supBaseEquiv_diagonalAt]
          rfl
      · simp
      · intro a b _ _ ha hb
        simpa using Subgroup.mul_mem _ ha hb
      · intro a _ ha
        simpa using Subgroup.inv_mem _ ha

/-- All special join code semantics are now unconditional. -/
theorem specialJoinCodeSemantics
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H)
    (hclosed : SpecialJoinClosedObligation hfive C) :
    SpecialJoinCodeSemantics hfive C hclosed where
  cutter_eq := hjoin_cutter_eq hfive C

/-- Assemble the actual coded special-Sup model from exactly the outstanding
two-stage code semantics. -/
def hjoinModel
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H)
    (hclosed : SpecialJoinClosedObligation hfive C)
    (S : SpecialJoinCodeSemantics hfive C hclosed) :
    Model pMark
      ((Star.graphSub ⊓ H.comap (MonoidHom.fst Conj.F₃ Conj.F₃)) ⊔
        Star.ProdBot) where
  data := hjoinData hfive C hclosed
  coded := hjoinSyntax hfive C
  ambientEquiv := Model.supLevel2Equiv (hgammaModel hfive C) botModel
  cutter_eq := S.cutter_eq
  marked_eq := Model.supLevel2Equiv_outputMark
    (hgammaModel hfive C) botModel

@[simp] theorem hjoinModel_coded
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H)
    (hclosed : SpecialJoinClosedObligation hfive C)
    (S : SpecialJoinCodeSemantics hfive C hclosed) :
    (hjoinModel hfive C hclosed S).coded = hjoinSyntax hfive C := rfl

/-- The actual coded strengthened witness produced by the special TransportStar
join.  Its sole semantic hypothesis is now the exact profinite closedness of
the semantic `joinL` cutter. -/
def hjoinModelOfClosed
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H)
    (hclosed : SpecialJoinClosedObligation hfive C) :
    Model pMark
      ((Star.graphSub ⊓ H.comap (MonoidHom.fst Conj.F₃ Conj.F₃)) ⊔
        Star.ProdBot) :=
  hjoinModel hfive C hclosed (specialJoinCodeSemantics hfive C hclosed)

@[simp] theorem hjoinModelOfClosed_coded
    (hfive : profiniteClosure fiveCutter = fiveCutter)
    {H : Subgroup Conj.F₃} (C : Model sourceMark H)
    (hclosed : SpecialJoinClosedObligation hfive C) :
    (hjoinModelOfClosed hfive C hclosed).coded = hjoinSyntax hfive C := rfl

end

end CodedTransportStarProfinite
end Higman
end GroupApproximation
