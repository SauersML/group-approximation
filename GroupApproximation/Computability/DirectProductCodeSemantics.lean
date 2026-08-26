import GroupApproximation.Computability.DirectProductCode
import GroupApproximation.Computability.PresentationCodeList
import GroupApproximation.Algebra.PresentedGroupRelabel
import GroupApproximation.Algebra.PresentedGroupEvaluation

/-!
# Semantics of the direct-product presentation code

`DirectProductCode.productCode` is a primitive-recursive list constructor.
This file identifies its carrier with the direct product of the two input
carriers, using exactly the two factor relator families and the rectangular
family of cross-generator commutators written by that constructor.
-/

namespace GroupApproximation
namespace DirectProductCodeSemantics

open scoped commutatorElement
open PresentationCodes PresentationCodeList PresentedGroupRelabel
open DirectProductCode RawWord

/-- Consecutive numbering of the two input alphabets in the product code. -/
def productGeneratorEquiv (c d : PresentationCode) :
    Fin (genCount c) ⊕ Fin (genCount d) ≃ Fin (genCount (productCode c d)) :=
  finSumFinEquiv.trans (finCongr (productCode_genCount c d).symm)

@[simp] theorem productGeneratorEquiv_inl (c d : PresentationCode)
    (i : Fin (genCount c)) :
    productGeneratorEquiv c d (Sum.inl i) =
      letterOf (productCode c d) i := by
  apply Fin.ext
  simp only [productGeneratorEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left,
    finCongr_apply, Fin.val_cast, letterOf, productCode_genCount]
  exact (Nat.mod_eq_of_lt
    (lt_of_lt_of_le i.isLt (Nat.le_add_right _ _))).symm

@[simp] theorem productGeneratorEquiv_inr (c d : PresentationCode)
    (j : Fin (genCount d)) :
    productGeneratorEquiv c d (Sum.inr j) =
      letterOf (productCode c d) (genCount c + j) := by
  apply Fin.ext
  simp only [productGeneratorEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right,
    finCongr_apply, Fin.val_cast, letterOf, productCode_genCount]
  exact (Nat.mod_eq_of_lt (Nat.add_lt_add_left j.isLt _)).symm

/-- The product code reads a normalized left word as the left summand word. -/
theorem wordOf_productCode_leftWord (c d : PresentationCode) (w : Raw) :
    wordOf (productCode c d) (leftWord c w) =
      relabel (productGeneratorEquiv c d)
        (FreeGroup.map Sum.inl (wordOf c w)) := by
  show FreeGroup.mk _ = _
  rw [wordOf, FreeGroup.map.mk, relabel, FreeGroup.map.mk]
  congr 1
  simp only [leftWord, List.map_map, Function.comp_def]
  refine List.map_congr_left fun p _ => ?_
  refine Prod.ext ?_ rfl
  rw [productGeneratorEquiv_inl]
  simp only [letterOf]

/-- The product code reads a shifted normalized right word as the right
summand word. -/
theorem wordOf_productCode_rightWord (c d : PresentationCode) (w : Raw) :
    wordOf (productCode c d) (rightWord c d w) =
      relabel (productGeneratorEquiv c d)
        (FreeGroup.map Sum.inr (wordOf d w)) := by
  show FreeGroup.mk _ = _
  rw [wordOf, FreeGroup.map.mk, relabel, FreeGroup.map.mk]
  congr 1
  simp only [rightWord, List.map_map, Function.comp_def]
  refine List.map_congr_left fun p _ => ?_
  refine Prod.ext ?_ rfl
  rw [productGeneratorEquiv_inr]
  simp only [letterOf]

/-- One raw rectangular relator is the corresponding commutator of the two
renumbered free generators. -/
theorem wordOf_productCode_commutatorWord (c d : PresentationCode)
    (i : Fin (genCount c)) (j : Fin (genCount d)) :
    wordOf (productCode c d) (commutatorWord c i j) =
      ⁅FreeGroup.of (productGeneratorEquiv c d (Sum.inl i)),
        FreeGroup.of (productGeneratorEquiv c d (Sum.inr j))⁆ := by
  simp only [commutatorWord, wordOf_cons_pos, wordOf_cons_neg, wordOf_nil,
    mul_one, productGeneratorEquiv_inl, productGeneratorEquiv_inr,
    commutatorElement_def]
  group

/-! ## The semantic presentation on the sum alphabet -/

abbrev codeRels (c : PresentationCode) :
    Set (FreeGroup (Fin (genCount c))) :=
  ((relatorFinset c : Finset (FreeGroup (Fin (genCount c)))) :
    Set (FreeGroup (Fin (genCount c))))

def crossRels (c d : PresentationCode) :
    Set (FreeGroup (Fin (genCount c) ⊕ Fin (genCount d))) :=
  Set.range fun p : Fin (genCount c) × Fin (genCount d) =>
    ⁅(FreeGroup.of (Sum.inl p.1) :
        FreeGroup (Fin (genCount c) ⊕ Fin (genCount d))),
      FreeGroup.of (Sum.inr p.2)⁆

def productRels (c d : PresentationCode) :
    Set (FreeGroup (Fin (genCount c) ⊕ Fin (genCount d))) :=
  (relabelRels Sum.inl (codeRels c) ∪
      relabelRels Sum.inr (codeRels d)) ∪
    crossRels c d

abbrev ProductPresentation (c d : PresentationCode) : Type :=
  PresentedGroup (productRels c d)

def toProductGenerator (c d : PresentationCode) :
    Fin (genCount c) ⊕ Fin (genCount d) → Carrier c × Carrier d
  | Sum.inl i => (PresentedGroup.of i, 1)
  | Sum.inr j => (1, PresentedGroup.of j)

theorem lift_toProductGenerator_inl (c d : PresentationCode)
    (w : FreeGroup (Fin (genCount c))) :
    FreeGroup.lift (toProductGenerator c d) (relabel Sum.inl w) =
      (PresentedGroup.mk (codeRels c) w, 1) := by
  refine freeGroup_hom_eq_on_generators
    (f := (FreeGroup.lift (toProductGenerator c d)).comp (relabel Sum.inl))
    (g := (PresentedGroup.mk (codeRels c)).prod
      (1 : FreeGroup (Fin (genCount c)) →* Carrier d)) ?_ w
  intro i
  simp [toProductGenerator, relabel, PresentedGroup.of]

theorem lift_toProductGenerator_inr (c d : PresentationCode)
    (w : FreeGroup (Fin (genCount d))) :
    FreeGroup.lift (toProductGenerator c d) (relabel Sum.inr w) =
      (1, PresentedGroup.mk (codeRels d) w) := by
  refine freeGroup_hom_eq_on_generators
    (f := (FreeGroup.lift (toProductGenerator c d)).comp (relabel Sum.inr))
    (g := (1 : FreeGroup (Fin (genCount d)) →* Carrier c).prod
      (PresentedGroup.mk (codeRels d))) ?_ w
  intro j
  simp [toProductGenerator, relabel, PresentedGroup.of]

theorem toProductGenerator_kills (c d : PresentationCode) :
    ∀ r ∈ productRels c d,
      FreeGroup.lift (toProductGenerator c d) r = 1 := by
  rintro r ((hr | hr) | hr)
  · obtain ⟨r, hr, rfl⟩ := hr
    rw [lift_toProductGenerator_inl]
    rw [PresentedGroup.mk_eq_one_iff.mpr
      (Subgroup.subset_normalClosure hr)]
    rfl
  · obtain ⟨r, hr, rfl⟩ := hr
    rw [lift_toProductGenerator_inr]
    rw [PresentedGroup.mk_eq_one_iff.mpr
      (Subgroup.subset_normalClosure hr)]
    rfl
  · obtain ⟨⟨i, j⟩, rfl⟩ := hr
    ext <;> simp [toProductGenerator, commutatorElement_def]

/-- The canonical map from the semantic product presentation to the actual
direct product. -/
def toProduct (c d : PresentationCode) :
    ProductPresentation c d →* Carrier c × Carrier d :=
  PresentedGroup.toGroup (toProductGenerator_kills c d)

@[simp] theorem toProduct_of_inl (c d : PresentationCode)
    (i : Fin (genCount c)) :
    toProduct c d (PresentedGroup.of (Sum.inl i)) =
      ((PresentedGroup.of i, 1) : Carrier c × Carrier d) :=
  PresentedGroup.toGroup.of _

@[simp] theorem toProduct_of_inr (c d : PresentationCode)
    (j : Fin (genCount d)) :
    toProduct c d (PresentedGroup.of (Sum.inr j)) =
      ((1, PresentedGroup.of j) : Carrier c × Carrier d) :=
  PresentedGroup.toGroup.of _

def leftGenerator (c d : PresentationCode) (i : Fin (genCount c)) :
    ProductPresentation c d :=
  PresentedGroup.of (Sum.inl i)

def rightGenerator (c d : PresentationCode) (j : Fin (genCount d)) :
    ProductPresentation c d :=
  PresentedGroup.of (Sum.inr j)

theorem leftGenerator_kills (c d : PresentationCode) :
    ∀ r ∈ codeRels c, FreeGroup.lift (leftGenerator c d) r = 1 := by
  intro r hr
  have hrel : relabel Sum.inl r ∈ productRels c d :=
    Or.inl (Or.inl ⟨r, hr, rfl⟩)
  have hmk : PresentedGroup.mk (productRels c d) (relabel Sum.inl r) = 1 :=
    PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure hrel)
  rw [show FreeGroup.lift (leftGenerator c d) r =
      PresentedGroup.mk (productRels c d) (relabel Sum.inl r) by
    refine freeGroup_hom_eq_on_generators
      (f := FreeGroup.lift (leftGenerator c d))
      (g := (PresentedGroup.mk (productRels c d)).comp (relabel Sum.inl)) ?_ r
    intro i
    simp [leftGenerator, relabel, PresentedGroup.of]]
  exact hmk

theorem rightGenerator_kills (c d : PresentationCode) :
    ∀ r ∈ codeRels d, FreeGroup.lift (rightGenerator c d) r = 1 := by
  intro r hr
  have hrel : relabel Sum.inr r ∈ productRels c d :=
    Or.inl (Or.inr ⟨r, hr, rfl⟩)
  have hmk : PresentedGroup.mk (productRels c d) (relabel Sum.inr r) = 1 :=
    PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure hrel)
  rw [show FreeGroup.lift (rightGenerator c d) r =
      PresentedGroup.mk (productRels c d) (relabel Sum.inr r) by
    refine freeGroup_hom_eq_on_generators
      (f := FreeGroup.lift (rightGenerator c d))
      (g := (PresentedGroup.mk (productRels c d)).comp (relabel Sum.inr)) ?_ r
    intro j
    simp [rightGenerator, relabel, PresentedGroup.of]]
  exact hmk

def leftHom (c d : PresentationCode) :
    Carrier c →* ProductPresentation c d :=
  PresentedGroup.toGroup (leftGenerator_kills c d)

def rightHom (c d : PresentationCode) :
    Carrier d →* ProductPresentation c d :=
  PresentedGroup.toGroup (rightGenerator_kills c d)

@[simp] theorem leftHom_of (c d : PresentationCode)
    (i : Fin (genCount c)) :
    leftHom c d (PresentedGroup.of i) = PresentedGroup.of (Sum.inl i) :=
  PresentedGroup.toGroup.of _

@[simp] theorem rightHom_of (c d : PresentationCode)
    (j : Fin (genCount d)) :
    rightHom c d (PresentedGroup.of j) = PresentedGroup.of (Sum.inr j) :=
  PresentedGroup.toGroup.of _

theorem left_right_generator_commute (c d : PresentationCode)
    (i : Fin (genCount c)) (j : Fin (genCount d)) :
    Commute (leftHom c d (PresentedGroup.of i))
      (rightHom c d (PresentedGroup.of j)) := by
  rw [leftHom_of, rightHom_of, ← commutatorElement_eq_one_iff_commute]
  exact PresentedGroup.mk_eq_one_iff.mpr
    (Subgroup.subset_normalClosure
      (Or.inr ⟨(i, j), rfl⟩))

theorem left_right_commute (c d : PresentationCode)
    (x : Carrier c) (y : Carrier d) :
    Commute (leftHom c d x) (rightHom c d y) := by
  have hright : ∀ i : Fin (genCount c), ∀ y : Carrier d,
      Commute (leftHom c d (PresentedGroup.of i)) (rightHom c d y) := by
    intro i y
    have hle : Subgroup.closure
        (Set.range (PresentedGroup.of : Fin (genCount d) → Carrier d)) ≤
        Subgroup.comap (rightHom c d)
          (Subgroup.centralizer {leftHom c d (PresentedGroup.of i)}) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      exact Subgroup.mem_comap.mpr
        (Subgroup.mem_centralizer_iff.mpr fun _ h => by
          rw [Set.mem_singleton_iff.mp h]
          exact left_right_generator_commute c d i j)
    rw [PresentedGroup.closure_range_of] at hle
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_comap.mp (hle (Subgroup.mem_top y)))) _ rfl
  have hle : Subgroup.closure
      (Set.range (PresentedGroup.of : Fin (genCount c) → Carrier c)) ≤
      Subgroup.comap (leftHom c d)
        (Subgroup.centralizer {rightHom c d y}) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_comap.mpr
      (Subgroup.mem_centralizer_iff.mpr fun _ h => by
        rw [Set.mem_singleton_iff.mp h]
        exact (hright i y).symm)
  rw [PresentedGroup.closure_range_of] at hle
  exact ((Subgroup.mem_centralizer_iff.mp
    (Subgroup.mem_comap.mp (hle (Subgroup.mem_top x)))) _ rfl).symm

/-- The inverse map, multiplying the commuting images of the two factors. -/
def fromProduct (c d : PresentationCode) :
    Carrier c × Carrier d →* ProductPresentation c d :=
  MonoidHom.noncommCoprod (leftHom c d) (rightHom c d)
    (left_right_commute c d)

theorem toProduct_comp_leftHom (c d : PresentationCode) :
    (toProduct c d).comp (leftHom c d) = MonoidHom.inl (Carrier c) (Carrier d) := by
  refine MonoidHom.eq_of_eqOn_dense (PresentedGroup.closure_range_of (codeRels c)) ?_
  rintro _ ⟨i, rfl⟩
  simp

theorem toProduct_comp_rightHom (c d : PresentationCode) :
    (toProduct c d).comp (rightHom c d) = MonoidHom.inr (Carrier c) (Carrier d) := by
  refine MonoidHom.eq_of_eqOn_dense (PresentedGroup.closure_range_of (codeRels d)) ?_
  rintro _ ⟨j, rfl⟩
  simp

theorem toProduct_fromProduct (c d : PresentationCode)
    (x : Carrier c × Carrier d) :
    toProduct c d (fromProduct c d x) = x := by
  rw [fromProduct, MonoidHom.noncommCoprod_apply, map_mul]
  have hleft := DFunLike.congr_fun (toProduct_comp_leftHom c d) x.1
  have hright := DFunLike.congr_fun (toProduct_comp_rightHom c d) x.2
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply,
    MonoidHom.inr_apply] at hleft hright
  rw [hleft, hright]
  simp

theorem fromProduct_toProduct (c d : PresentationCode)
    (x : ProductPresentation c d) :
    fromProduct c d (toProduct c d x) = x := by
  let f := (fromProduct c d).comp (toProduct c d)
  have h : f = MonoidHom.id (ProductPresentation c d) := by
    refine MonoidHom.eq_of_eqOn_dense
      (PresentedGroup.closure_range_of (productRels c d)) ?_
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i =>
        change fromProduct c d (toProduct c d (PresentedGroup.of (Sum.inl i))) = _
        rw [toProduct_of_inl, fromProduct, MonoidHom.noncommCoprod_apply]
        simp
    | inr j =>
        change fromProduct c d (toProduct c d (PresentedGroup.of (Sum.inr j))) = _
        rw [toProduct_of_inr, fromProduct, MonoidHom.noncommCoprod_apply]
        simp
  change f x = x
  exact DFunLike.congr_fun h x

/-- The sum-alphabet presentation with factor relators and all cross-basis
commutators is the direct product. -/
noncomputable def productPresentationEquiv (c d : PresentationCode) :
    ProductPresentation c d ≃* Carrier c × Carrier d :=
  { toProduct c d with
    invFun := fromProduct c d
    left_inv := fromProduct_toProduct c d
    right_inv := toProduct_fromProduct c d }

end DirectProductCodeSemantics
end GroupApproximation
