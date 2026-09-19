import GroupApproximation.Computability.AdianRabinVariantTransform
import GroupApproximation.Computability.CStarRecognitionConsequences

/-!
# The Adian--Rabin theorem, for an arbitrary Markov property

`Computability.AdianRabinVariantTransform` carries out the Adian--Rabin
construction in full --- all four fields of a
`MarkovMFConsequences.AdianRabinReduction`, including the computability of the
transformation --- but only for one property, operator-MF, with one fixed
forbidden code.  Nothing in that construction is about operator-MF.  This file
abstracts it.

Read the construction again and every group-theoretic step is
property-independent:

* `RabinVariantMF.collapseEquiv` --- when the word dies the constructed group
  is **free**;
* `RabinVariantPresentation.srcToPres_injective_of_ne_one` --- when it
  survives the source group **embeds** in the constructed group;
* `RabinConstructionSource.inclRight_injective` --- the right factor embeds in
  a free product;
* `RawTransformPrimrec.computable_rawTransform` --- already stated for an
  arbitrary forbidden code `d`.

So the only things a property has to supply are the Markov clauses, and they
are exactly `MarkovData` below: heredity along injections, truth on free
groups, one positive code, and one forbidden code the property fails.  That is
the Adian--Rabin theorem.

* `MarkovData` --- the input;
* `codeProperty` --- the induced property of presentation codes;
* `reduction` --- **the theorem**: an `AdianRabinReduction` from the word
  problem to that property;
* `recognition_undecidable_of_wordProblem`, `negative_side_not_re_of_wordProblem`
  --- its two consequences;
* `groupCStarAdianRabinReductions` --- the five-fold instance, which is what
  `CStarRecognitionConsequences.GroupCStarAdianRabinReductions` was standing in
  for.

The word problem stays a hypothesis throughout, as it must: Adian--Rabin is a
reduction theorem, and the undecidability it reduces from is Novikov--Boone.

## Manuscript status

Discharges the Adian--Rabin row of `metadata/LITERATURE_QUARANTINE.md`:
`GroupCStarAdianRabinReductions` is no longer a typed citation, it is
constructed from Markov data by the theorem below.
-/

namespace GroupApproximation
namespace AdianRabinGeneral

open PresentationCodes PresentationCodeList CoprodCode RabinVariantCode
open PresentedGroupRelabel RabinConstructionSource AdianRabinWordProblem
open RabinVariantPresentation RabinVariantMF MarkovMFConsequences

/-! ## The input -/

/-- **Markov data for a property of groups.**  These are exactly the clauses
the Adian--Rabin construction consumes: the property passes to subgroups, it
holds of free groups, and some finite presentation fails it.

Isomorphism invariance is not a separate field --- an isomorphism is an
injective homomorphism, in both directions. -/
structure MarkovData (P : (H : Type) → [Group H] → Prop) where
  /-- The property passes to subgroups. -/
  hereditary : ∀ {H K : Type} [Group H] [Group K] (f : H →* K),
    Function.Injective f → P K → P H
  /-- The property holds of every countably generated free group.  This is the
  positive clause the *variant* construction needs: when the word dies, the
  group it presents is free. -/
  free : ∀ (α : Type) [Countable α], P (FreeGroup α)
  /-- A code the property holds of, for the Markov witness. -/
  positiveCode : PresentationCode
  /-- Its proof. -/
  positive : P (Carrier positiveCode)
  /-- A code the property fails --- the forbidden group. -/
  forbidden : PresentationCode
  /-- Its proof. -/
  forbidden_not : ¬ P (Carrier forbidden)

/-- **Markov data is closed under conjunction.**  Heredity and truth on free
groups are both conjunctive, and either forbidden code still works, so a
common positive code is the only new input. -/
def MarkovData.and {P Q : (H : Type) → [Group H] → Prop}
    (DP : MarkovData P) (DQ : MarkovData Q) (posCode : PresentationCode)
    (hP : P (Carrier posCode)) (hQ : Q (Carrier posCode)) :
    MarkovData (fun (H : Type) (_ : Group H) ↦ P H ∧ Q H) where
  hereditary f hf hK := ⟨DP.hereditary f hf hK.1, DQ.hereditary f hf hK.2⟩
  free α _ := ⟨DP.free α, DQ.free α⟩
  positiveCode := posCode
  positive := ⟨hP, hQ⟩
  forbidden := DP.forbidden
  forbidden_not := fun h ↦ DP.forbidden_not h.1

/-- The property of presentation codes induced by a property of groups. -/
def codeProperty (P : (H : Type) → [Group H] → Prop) :
    PresentationProperty PresentationCode :=
  fun c ↦ P (Carrier c)

variable {P : (H : Type) → [Group H] → Prop} (D : MarkovData P)

/-! ## The transformation -/

/-- **The word problem of the input is the word problem of the free product.**
`AdianRabinVariantTransform.coprod_mk_eq_one_iff` at an arbitrary forbidden
code; the proof never mentions which code it is. -/
theorem coprod_mk_eq_one_iff (d : PresentationCode) (c : PresentationCode)
    (w : List (ℕ × Bool)) :
    PresentedGroup.mk {x | x ∈ relatorListOf (coprodCode c d)}
        (wordOf (coprodCode c d) (normWord c w)) = 1
      ↔ WordProblem c w := by
  rw [wordOf_coprodCode, relSet_coprodCode, mk_relabel_eq_one_iff,
    mk_map_inl_eq_one_iff, WordProblem]
  -- `coe_relatorFinset` is stated about the coercion of the finset, which is
  -- what `relatorSet` is definitionally; ascribing it at the unfolded type is
  -- what puts its pattern in the goal.
  have hset : relatorSet c = {x | x ∈ relatorListOf c} := coe_relatorFinset c
  rw [hset]

/-- The transformation: free-product with the forbidden code, then run the
variant construction on the word. -/
noncomputable def transform (x : PresentationCode × List (ℕ × Bool)) :
    PresentationCode :=
  variantCode (coprodCode x.1 D.forbidden) (normWord x.1 x.2)

/-- **The collapse clause, for an arbitrary Markov property.**  If the word
dies, the constructed group is free, so the property holds. -/
theorem holds_transform_of_wordProblem (c : PresentationCode)
    (w : List (ℕ × Bool)) (hw : WordProblem c w) :
    codeProperty P (transform D (c, w)) := by
  have h0 : PresentedGroup.mk {x | x ∈ relatorListOf (coprodCode c D.forbidden)}
      (wordOf (coprodCode c D.forbidden) (normWord c w)) = 1 :=
    (coprod_mk_eq_one_iff D.forbidden c w).2 hw
  have hfree : P (Pres {x | x ∈ relatorListOf (coprodCode c D.forbidden)}
      (wordOf (coprodCode c D.forbidden) (normWord c w))) :=
    D.hereditary (collapseEquiv _ _ h0).symm.toMonoidHom
      (collapseEquiv _ _ h0).symm.injective (D.free _)
  exact D.hereditary
    (variantCodeEquiv (coprodCode c D.forbidden) (normWord c w)).toMonoidHom
    (variantCodeEquiv _ _).injective hfree

/-- **The embedding clause, for an arbitrary Markov property.**  If the word
survives, the forbidden group embeds in the constructed group, so the property
fails. -/
theorem wordProblem_of_holds_transform (c : PresentationCode)
    (w : List (ℕ × Bool)) (hP : codeProperty P (transform D (c, w))) :
    WordProblem c w := by
  by_contra hw
  have hne : PresentedGroup.mk {x | x ∈ relatorListOf (coprodCode c D.forbidden)}
      (wordOf (coprodCode c D.forbidden) (normWord c w)) ≠ 1 :=
    fun h ↦ hw ((coprod_mk_eq_one_iff D.forbidden c w).1 h)
  have h1 : P (Pres {x | x ∈ relatorListOf (coprodCode c D.forbidden)}
      (wordOf (coprodCode c D.forbidden) (normWord c w))) :=
    D.hereditary
      (variantCodeEquiv (coprodCode c D.forbidden) (normWord c w)).symm.toMonoidHom
      (variantCodeEquiv _ _).symm.injective hP
  have h2 : P (PresentedGroup {x | x ∈ relatorListOf (coprodCode c D.forbidden)}) :=
    D.hereditary (srcToPres _ _) (srcToPres_injective_of_ne_one _ _ hne) h1
  have h3 : P (Carrier (coprodCode c D.forbidden)) :=
    D.hereditary (carrierEquivList (coprodCode c D.forbidden)).toMonoidHom
      (carrierEquivList _).injective h2
  have h4 : P (CoprodPresented {x | x ∈ relatorListOf c}
      {x | x ∈ relatorListOf D.forbidden}) :=
    D.hereditary (coprodCodeEquiv c D.forbidden).symm.toMonoidHom
      (coprodCodeEquiv c D.forbidden).symm.injective h3
  have h5 : P (PresentedGroup {x | x ∈ relatorListOf D.forbidden}) :=
    D.hereditary (inclRight _ _) (inclRight_injective _ _) h4
  exact D.forbidden_not
    (D.hereditary (carrierEquivList D.forbidden).toMonoidHom
      (carrierEquivList D.forbidden).injective h5)

/-- Correctness of the transformation. -/
theorem correct (x : PresentationCode × List (ℕ × Bool)) :
    codeProperty P (transform D x) ↔ WordProblem x.1 x.2 :=
  ⟨fun h ↦ wordProblem_of_holds_transform D x.1 x.2 h,
    fun h ↦ holds_transform_of_wordProblem D x.1 x.2 h⟩

/-! ## The same transformation, as list surgery -/

/-- The transformation a program can actually build. -/
noncomputable def rawTransform (x : PresentationCode × List (ℕ × Bool)) :
    PresentationCode :=
  RawTransform.rawTransform x.1 D.forbidden x.2

/-- Correctness for the list-surgery form. -/
theorem correct_raw (x : PresentationCode × List (ℕ × Bool)) :
    codeProperty P (rawTransform D x) ↔ WordProblem x.1 x.2 := by
  constructor
  · intro h
    refine (correct D x).1 ?_
    exact D.hereditary
      (RawTransform.rawCarrierEquiv x.1 D.forbidden x.2).symm.toMonoidHom
      (RawTransform.rawCarrierEquiv x.1 D.forbidden x.2).symm.injective h
  · intro h
    exact D.hereditary
      (RawTransform.rawCarrierEquiv x.1 D.forbidden x.2).toMonoidHom
      (RawTransform.rawCarrierEquiv x.1 D.forbidden x.2).injective
      ((correct D x).2 h)

/-! ## The theorem -/

/-- **The Adian--Rabin theorem.**  Every Markov property of finite
presentations is many-one reducible from the word problem, by a computable
transformation of codes. -/
noncomputable def reduction :
    AdianRabinReduction AdianRabinWordProblem.wordProblemPred
      (codeProperty P) where
  markov :=
    { positiveCode := D.positiveCode
      positive := D.positive
      negativeCode := D.forbidden
      negative := D.forbidden_not }
  transform := rawTransform D
  transform_computable := RawTransformPrimrec.computable_rawTransform D.forbidden
  correct := correct_raw D

include D in
/-- **Recognition of a Markov property is undecidable**, given only that the
word problem is. -/
theorem recognition_undecidable_of_wordProblem
    (h : ¬ ComputablePred AdianRabinWordProblem.wordProblemPred) :
    ¬ ComputablePred (codeProperty P) :=
  recognition_undecidable (reduction D) h

include D in
/-- The negative side is not even recursively enumerable. -/
theorem negative_side_not_re_of_wordProblem
    (h : ¬ REPred (fun x ↦ ¬ AdianRabinWordProblem.wordProblemPred x)) :
    ¬ REPred (fun c ↦ ¬ codeProperty P c) :=
  negative_side_not_re (reduction D) h

/-! ## The five group-C⋆ recognition predicates -/

/-- The five recognition predicates induced by five properties of groups. -/
def cstarPredicates (P₁ P₂ P₃ P₄ P₅ : (H : Type) → [Group H] → Prop) :
    CStarRecognitionConsequences.GroupCStarRecognitionPredicates
      PresentationCode where
  reducedMF := codeProperty P₁
  maximalMF := codeProperty P₂
  maximalFinite := codeProperty P₃
  maximalStablyFinite := codeProperty P₄
  maximalDirectlyFinite := codeProperty P₅

/-- **`CStarRecognitionConsequences.GroupCStarAdianRabinReductions`, built.**
The structure was a typed stand-in for the Adian--Rabin theorem; with the
theorem proved it is a construction out of Markov data, and the operator
algebra enters only through those five inputs. -/
noncomputable def groupCStarAdianRabinReductions
    {P₁ P₂ P₃ P₄ P₅ : (H : Type) → [Group H] → Prop}
    (D₁ : MarkovData P₁) (D₂ : MarkovData P₂) (D₃ : MarkovData P₃)
    (D₄ : MarkovData P₄) (D₅ : MarkovData P₅) :
    CStarRecognitionConsequences.GroupCStarAdianRabinReductions
      AdianRabinWordProblem.wordProblemPred
      (cstarPredicates P₁ P₂ P₃ P₄ P₅) where
  reducedMF := reduction D₁
  maximalMF := reduction D₂
  maximalFinite := reduction D₃
  maximalStablyFinite := reduction D₄
  maximalDirectlyFinite := reduction D₅

end AdianRabinGeneral
end GroupApproximation
