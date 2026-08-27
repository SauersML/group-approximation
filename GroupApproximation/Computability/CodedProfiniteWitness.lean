import GroupApproximation.Computability.BenignInfCodeSubgroupSemantics
import GroupApproximation.Computability.BenignComapCodeSemantics
import GroupApproximation.Higman.ProfiniteBenignWitness

/-!
# Finite syntax attached to strengthened benign witnesses

The effective Higman compiler needs more than an abstract
`ProfiniteBenignWitness`: it needs a finite presentation code for the witness
ambient, raw words generating its cutter, and raw representatives of the six
marks used by the operation calculus.  This structure records the exact
semantic contract.  It deliberately contains no generic image or join
constructor; those require additional profinite theorems.
-/

namespace GroupApproximation
namespace CodedProfiniteWitness

noncomputable section

open PresentationCodes BenignInfCode
open BenignInfCodeSemantics BenignInfCodeSubgroupSemantics

abbrev MarkCount := Fin 6

/-- A six-mark finite presentation model of a strengthened benign witness. -/
structure Model {G : Type} [Group G] (mark : MarkCount → G)
    (H : Subgroup G) where
  data : Higman.ProfiniteBenignWitness H
  coded : WitnessSyntax
  ambientEquiv : Carrier coded.1 ≃* data.witness.K
  cutter_eq :
    (wordSubgroup coded.1 coded.2.1).map ambientEquiv.toMonoidHom =
      data.witness.L
  marked_eq : ∀ i : MarkCount,
    ambientEquiv (evalWord coded.1 (coded.2.2.getD i [])) =
      data.witness.emb (mark i)

/-- A coded finite-presentation model of a profinitely full overgroup, with
six marked source elements.  This is the left input of the safe preimage
constructor. -/
structure OvergroupModel {G : Type} [Group G] (mark : MarkCount → G)
    (u : Higman.ProfiniteFPOvergroup G) where
  code : PresentationCode
  marks : List BenignInfCode.Raw
  ambientEquiv : Carrier code ≃* u.overgroup.K
  marked_eq : ∀ i : MarkCount,
    ambientEquiv (evalWord code (marks.getD i [])) = u.overgroup.emb (mark i)

namespace Model

variable {G : Type} [Group G] {mark : MarkCount → G}
variable {H₁ H₂ : Subgroup G}

/-- Product of two ambient equivalences. -/
def prodEquiv {K₁ K₂ L₁ L₂ : Type}
    [Group K₁] [Group K₂] [Group L₁] [Group L₂]
    (e₁ : K₁ ≃* L₁) (e₂ : K₂ ≃* L₂) :
    K₁ × K₂ ≃* L₁ × L₂ where
  toFun x := (e₁ x.1, e₂ x.2)
  invFun x := (e₁.symm x.1, e₂.symm x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_mul' _ _ := by simp

theorem map_prodEquiv {K₁ K₂ L₁ L₂ : Type}
    [Group K₁] [Group K₂] [Group L₁] [Group L₂]
    (e₁ : K₁ ≃* L₁) (e₂ : K₂ ≃* L₂)
    (A : Subgroup K₁) (B : Subgroup K₂) :
    (A.prod B).map (prodEquiv e₁ e₂).toMonoidHom =
      (A.map e₁.toMonoidHom).prod (B.map e₂.toMonoidHom) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_prod.mp hx
    exact Subgroup.mem_prod.mpr
      ⟨Subgroup.mem_map.mpr ⟨x.1, hx₁, rfl⟩,
        Subgroup.mem_map.mpr ⟨x.2, hx₂, rfl⟩⟩
  · intro hz
    obtain ⟨hz₁, hz₂⟩ := Subgroup.mem_prod.mp hz
    obtain ⟨x₁, hx₁, hx₁eq⟩ := Subgroup.mem_map.mp hz₁
    obtain ⟨x₂, hx₂, hx₂eq⟩ := Subgroup.mem_map.mp hz₂
    exact Subgroup.mem_map.mpr
      ⟨(x₁, x₂), Subgroup.mem_prod.mpr ⟨hx₁, hx₂⟩,
        Prod.ext hx₁eq hx₂eq⟩

theorem wordSubgroup_generatorWords_top (c : PresentationCode) :
    wordSubgroup c (BenignSupCode.generatorWords c) = ⊤ := by
  apply top_unique
  rw [← PresentedGroup.closure_range_of (DirectProductCodeSemantics.codeRels c)]
  apply (Subgroup.closure_le (wordSubgroup c (BenignSupCode.generatorWords c))).2
  rintro _ ⟨i, rfl⟩
  have heval : evalWord c ([(i, true)] : BenignInfCode.Raw) =
      (PresentedGroup.of i : Carrier c) := by
    rw [BenignComapCodeSemantics.evalWord_generatorWord]
    congr 1
    apply Fin.ext
    exact RawWord.letterOf_val_of_lt c i.isLt
  rw [← heval]
  apply evalWord_mem_wordSubgroup c (BenignSupCode.generatorWords c)
  unfold BenignSupCode.generatorWords
  apply List.mem_map.mpr
  refine ⟨(i : ℕ), List.mem_range.mpr i.isLt, ?_⟩
  rfl

@[simp] theorem diagonalMarks_getD (x : BenignInfCode.Input) (i : MarkCount) :
    (BenignInfCode.diagonalMarks x).getD i [] = BenignInfCode.diagonalAt x i := by
  fin_cases i <;> rfl

/-- The computed preimage cutter is exactly `top × L` under the concrete
product-code equivalence. -/
theorem map_wordSubgroup_comap_cutting (x : BenignComapCode.Input) :
    (wordSubgroup (BenignComapCode.transform x).1
      (BenignComapCode.transform x).2.1).map
        (DirectProductCodeSemantics.productCodeEquiv
          (leftCode x) (rightCode x)).toMonoidHom =
      (⊤ : Subgroup (Carrier (leftCode x))).prod
        (wordSubgroup (rightCode x) (rightCutter x)) := by
  let x' : BenignInfCode.Input :=
    ((leftCode x, (BenignSupCode.generatorWords (leftCode x), leftMarks x)), x.2)
  have h := map_wordSubgroup_transform_cutting x'
  change _ =
    (wordSubgroup (leftCode x) (BenignSupCode.generatorWords (leftCode x))).prod
      (wordSubgroup (rightCode x) (rightCutter x)) at h
  rw [wordSubgroup_generatorWords_top] at h
  exact h

/-- The code-level direct product implements the strengthened intersection
constructor exactly. -/
def inf (C₁ : Model mark H₁) (C₂ : Model mark H₂) :
    Model mark (H₁ ⊓ H₂) where
  data := Higman.ProfiniteBenignWitness.inf C₁.data C₂.data
  coded := BenignInfCode.transform (C₁.coded, C₂.coded)
  ambientEquiv := by
    change Carrier (DirectProductCode.productCode C₁.coded.1 C₂.coded.1) ≃*
      (C₁.data.witness.K × C₂.data.witness.K)
    exact
      (DirectProductCodeSemantics.productCodeEquiv C₁.coded.1 C₂.coded.1).trans
        (prodEquiv C₁.ambientEquiv C₂.ambientEquiv)
  cutter_eq := by
    change
      (wordSubgroup
        (DirectProductCode.productCode C₁.coded.1 C₂.coded.1)
        (BenignInfCode.leftCuttingWords (C₁.coded, C₂.coded) ++
          BenignInfCode.rightCuttingWords (C₁.coded, C₂.coded))).map
          ((DirectProductCodeSemantics.productCodeEquiv
            C₁.coded.1 C₂.coded.1).trans
              (prodEquiv C₁.ambientEquiv C₂.ambientEquiv)).toMonoidHom =
        C₁.data.witness.L.prod C₂.data.witness.L
    change
      (wordSubgroup
        (DirectProductCode.productCode C₁.coded.1 C₂.coded.1)
        (BenignInfCode.leftCuttingWords (C₁.coded, C₂.coded) ++
          BenignInfCode.rightCuttingWords (C₁.coded, C₂.coded))).map
          ((prodEquiv C₁.ambientEquiv C₂.ambientEquiv).toMonoidHom.comp
            (DirectProductCodeSemantics.productCodeEquiv
              C₁.coded.1 C₂.coded.1).toMonoidHom) = _
    rw [← Subgroup.map_map]
    calc
      ((wordSubgroup
          (DirectProductCode.productCode C₁.coded.1 C₂.coded.1)
          (BenignInfCode.leftCuttingWords (C₁.coded, C₂.coded) ++
            BenignInfCode.rightCuttingWords (C₁.coded, C₂.coded))).map
          (DirectProductCodeSemantics.productCodeEquiv
            C₁.coded.1 C₂.coded.1).toMonoidHom).map
            (prodEquiv C₁.ambientEquiv C₂.ambientEquiv).toMonoidHom =
        ((wordSubgroup C₁.coded.1 C₁.coded.2.1).prod
          (wordSubgroup C₂.coded.1 C₂.coded.2.1)).map
            (prodEquiv C₁.ambientEquiv C₂.ambientEquiv).toMonoidHom := by
              exact congrArg
                (fun S => S.map
                  (prodEquiv C₁.ambientEquiv C₂.ambientEquiv).toMonoidHom)
                (map_wordSubgroup_transform_cutting (C₁.coded, C₂.coded))
      _ = _ := by rw [map_prodEquiv, C₁.cutter_eq, C₂.cutter_eq]
  marked_eq := by
    intro i
    simp only [id_eq, BenignInfCode.transform_marks, diagonalMarks_getD]
    change (prodEquiv C₁.ambientEquiv C₂.ambientEquiv)
      (DirectProductCodeSemantics.productCodeEquiv C₁.coded.1 C₂.coded.1
        (evalWord (DirectProductCode.productCode C₁.coded.1 C₂.coded.1)
          (BenignInfCode.diagonalAt (C₁.coded, C₂.coded) i))) =
      (C₁.data.witness.emb (mark i), C₂.data.witness.emb (mark i))
    have hdiag :
      DirectProductCodeSemantics.productCodeEquiv C₁.coded.1 C₂.coded.1
          (evalWord (DirectProductCode.productCode C₁.coded.1 C₂.coded.1)
            (BenignInfCode.diagonalAt (C₁.coded, C₂.coded) i)) =
      (evalWord C₁.coded.1 (C₁.coded.2.2.getD i []),
        evalWord C₂.coded.1 (C₂.coded.2.2.getD i [])) := by
      exact productCodeEquiv_diagonalAt (C₁.coded, C₂.coded) (i : ℕ)
    rw [hdiag]
    change
      (C₁.ambientEquiv (evalWord C₁.coded.1 (C₁.coded.2.2.getD i [])),
        C₂.ambientEquiv (evalWord C₂.coded.1 (C₂.coded.2.2.getD i []))) = _
    exact Prod.ext (C₁.marked_eq i) (C₂.marked_eq i)

/-- The direct-product preimage constructor is fully code-level and preserves
all strengthened profinite fields. -/
def comap {N : Type} [Group N] (u : Higman.ProfiniteFPOvergroup G)
    (phi : G →* N) {H : Subgroup N}
    (A : OvergroupModel mark u)
    (C : Model (fun i => phi (mark i)) H) :
    Model mark (H.comap phi) where
  data := Higman.ProfiniteBenignWitness.comap u phi C.data
  coded := BenignComapCode.transform
    ((A.code, ([], A.marks)), C.coded)
  ambientEquiv := by
    change Carrier (DirectProductCode.productCode A.code C.coded.1) ≃*
      (u.overgroup.K × C.data.witness.K)
    exact
      (DirectProductCodeSemantics.productCodeEquiv A.code C.coded.1).trans
        (prodEquiv A.ambientEquiv C.ambientEquiv)
  cutter_eq := by
    change
      (wordSubgroup
        (DirectProductCode.productCode A.code C.coded.1)
        (BenignSupCode.leftGeneratorWords
            ((A.code, ([], A.marks)), C.coded) ++
          BenignInfCode.rightCuttingWords
            ((A.code, ([], A.marks)), C.coded))).map
          ((DirectProductCodeSemantics.productCodeEquiv A.code C.coded.1).trans
            (prodEquiv A.ambientEquiv C.ambientEquiv)).toMonoidHom =
        (⊤ : Subgroup u.overgroup.K).prod C.data.witness.L
    change
      (wordSubgroup
        (DirectProductCode.productCode A.code C.coded.1)
        (BenignSupCode.leftGeneratorWords
            ((A.code, ([], A.marks)), C.coded) ++
          BenignInfCode.rightCuttingWords
            ((A.code, ([], A.marks)), C.coded))).map
          ((prodEquiv A.ambientEquiv C.ambientEquiv).toMonoidHom.comp
            (DirectProductCodeSemantics.productCodeEquiv
              A.code C.coded.1).toMonoidHom) = _
    rw [← Subgroup.map_map]
    calc
      ((wordSubgroup
          (DirectProductCode.productCode A.code C.coded.1)
          (BenignSupCode.leftGeneratorWords
              ((A.code, ([], A.marks)), C.coded) ++
            BenignInfCode.rightCuttingWords
              ((A.code, ([], A.marks)), C.coded))).map
          (DirectProductCodeSemantics.productCodeEquiv
            A.code C.coded.1).toMonoidHom).map
            (prodEquiv A.ambientEquiv C.ambientEquiv).toMonoidHom =
        ((⊤ : Subgroup (Carrier A.code)).prod
          (wordSubgroup C.coded.1 C.coded.2.1)).map
            (prodEquiv A.ambientEquiv C.ambientEquiv).toMonoidHom := by
              exact congrArg
                (fun S => S.map
                  (prodEquiv A.ambientEquiv C.ambientEquiv).toMonoidHom)
                (map_wordSubgroup_comap_cutting
                  ((A.code, ([], A.marks)), C.coded))
      _ = _ := by
        rw [map_prodEquiv,
          Subgroup.map_top_of_surjective _ A.ambientEquiv.surjective,
          C.cutter_eq]
  marked_eq := by
    intro i
    simp only [id_eq, BenignComapCode.transform_marks, diagonalMarks_getD]
    change (prodEquiv A.ambientEquiv C.ambientEquiv)
      (DirectProductCodeSemantics.productCodeEquiv A.code C.coded.1
        (evalWord (DirectProductCode.productCode A.code C.coded.1)
          (BenignInfCode.diagonalAt
            ((A.code, ([], A.marks)), C.coded) i))) =
      (u.overgroup.emb (mark i), C.data.witness.emb (phi (mark i)))
    have hdiag :
      DirectProductCodeSemantics.productCodeEquiv A.code C.coded.1
          (evalWord (DirectProductCode.productCode A.code C.coded.1)
            (BenignInfCode.diagonalAt
              ((A.code, ([], A.marks)), C.coded) i)) =
      (evalWord A.code (A.marks.getD i []),
        evalWord C.coded.1 (C.coded.2.2.getD i [])) := by
      exact BenignComapCodeSemantics.productCodeEquiv_mark
        ((A.code, ([], A.marks)), C.coded) (i : ℕ)
    rw [hdiag]
    change
      (A.ambientEquiv (evalWord A.code (A.marks.getD i [])),
        C.ambientEquiv (evalWord C.coded.1 (C.coded.2.2.getD i []))) = _
    exact Prod.ext (A.marked_eq i) (C.marked_eq i)

end Model

end

end CodedProfiniteWitness
end GroupApproximation
