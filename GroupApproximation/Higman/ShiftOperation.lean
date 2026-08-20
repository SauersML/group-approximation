import GroupApproximation.Higman.SequenceSpace
import GroupApproximation.Higman.BenignAmbient

/-!
# Higman's operation `σ`

`σ B = {f | ∃ g ∈ B, ∀ i, f i = g (i-1)}` --- the shift.  This file proves
that the family of sets of sequences with benign subgroup is closed under it.

Unlike `ι` and `υ`, which are lattice identities, the shift is realized by an
*automorphism of `F₃`*:

    a ↦ a,   b ↦ c⁻¹ b c,   c ↦ c

sends the `i`-th row element to the `(i+1)`-st and fixes `a`, hence sends
`aElt f` to `aElt (σ f)`.  Benignness is preserved by images under injective
homomorphisms (`Benign.mapEmb`), so the closure follows once the
identification is made.

The identification needs one ordering fact: the support of a shifted sequence
is the shifted support, and sorting commutes with translation.  That is
`sort_map_add` below, proved by uniqueness of sorted lists.

The same pattern will serve every Higman operation that is induced by an
endomorphism of `F₃` fixing `a`.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

open GroupApproximation.Higman.Conj

/-! ## 1.  Sorting commutes with translation -/

theorem sort_map_add (s : Finset ℤ) (k : ℤ) :
    (s.map (Equiv.addRight k).toEmbedding).sort (· ≤ ·)
      = (s.sort (· ≤ ·)).map (fun i => i + k) := by
  refine List.eq_of_perm_of_sorted ?_ (Finset.sort_sorted _ _) ?_
  · refine List.Perm.trans (Finset.sort_perm_toList _ _) ?_
    refine List.Perm.symm (List.Perm.trans (List.Perm.map _
      (Finset.sort_perm_toList _ _)) ?_)
    rw [Finset.map_val, Multiset.map_map]
    rfl
  · refine List.Sorted.map (Finset.sort_sorted _ _) ?_
    intro x y hxy
    exact add_le_add_right hxy k

/-! ## 2.  The shift on sequences -/

/-- The shift of a sequence. -/
noncomputable def shiftSeq (f : E) : E :=
  Finsupp.equivMapDomain (Equiv.addRight (1 : ℤ)) f

@[simp] theorem shiftSeq_apply (f : E) (i : ℤ) : shiftSeq f i = f (i - 1) := by
  unfold shiftSeq
  rw [Finsupp.equivMapDomain_apply]
  rfl

theorem shiftSeq_support (f : E) :
    (shiftSeq f).support = f.support.map (Equiv.addRight (1 : ℤ)).toEmbedding := rfl

/-- The shift on the free group of the index set. -/
def shiftFree : FreeGroup ℤ →* FreeGroup ℤ :=
  FreeGroup.lift (fun i : ℤ => FreeGroup.of (i + 1))

@[simp] theorem shiftFree_of (i : ℤ) :
    shiftFree (FreeGroup.of i) = FreeGroup.of (i + 1) := by
  unfold shiftFree
  rw [FreeGroup.lift.of]

/-- **The coding intertwines the two shifts.** -/
theorem elt_shiftSeq (f : E) : elt (shiftSeq f) = shiftFree (elt f) := by
  unfold elt
  rw [shiftSeq_support, sort_map_add, List.map_map]
  rw [map_list_prod, List.map_map]
  refine congrArg List.prod ?_
  refine List.map_congr_left fun j _ => ?_
  show FreeGroup.of (j + 1) ^ (shiftSeq f (j + 1))
    = shiftFree (FreeGroup.of j ^ f j)
  rw [map_zpow, shiftFree_of, shiftSeq_apply]
  congr 2
  ring

/-! ## 3.  The automorphism of `F₃` -/

/-- The endomorphism realizing the shift. -/
def shiftAut : F₃ →* F₃ :=
  FreeGroup.lift (fun i : Fin 3 =>
    if i = 0 then a else if i = 1 then c⁻¹ * b * c else c)

/-- Its inverse. -/
def shiftAutInv : F₃ →* F₃ :=
  FreeGroup.lift (fun i : Fin 3 =>
    if i = 0 then a else if i = 1 then c * b * c⁻¹ else c)

@[simp] theorem shiftAut_a : shiftAut a = a := by
  unfold shiftAut a
  rw [FreeGroup.lift.of]
  simp

@[simp] theorem shiftAut_b : shiftAut b = c⁻¹ * b * c := by
  unfold shiftAut b
  rw [FreeGroup.lift.of]
  simp

@[simp] theorem shiftAut_c : shiftAut c = c := by
  unfold shiftAut c
  rw [FreeGroup.lift.of]
  simp

@[simp] theorem shiftAutInv_a : shiftAutInv a = a := by
  unfold shiftAutInv a
  rw [FreeGroup.lift.of]
  simp

@[simp] theorem shiftAutInv_b : shiftAutInv b = c * b * c⁻¹ := by
  unfold shiftAutInv b
  rw [FreeGroup.lift.of]
  simp

@[simp] theorem shiftAutInv_c : shiftAutInv c = c := by
  unfold shiftAutInv c
  rw [FreeGroup.lift.of]
  simp

theorem shiftAutInv_comp_shiftAut :
    shiftAutInv.comp shiftAut = MonoidHom.id F₃ := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i
  · show shiftAutInv (shiftAut a) = a
    rw [shiftAut_a, shiftAutInv_a]
  · show shiftAutInv (shiftAut b) = b
    rw [shiftAut_b, map_mul, map_mul, map_inv, shiftAutInv_b, shiftAutInv_c]
    group
  · show shiftAutInv (shiftAut c) = c
    rw [shiftAut_c, shiftAutInv_c]

theorem shiftAut_comp_shiftAutInv :
    shiftAut.comp shiftAutInv = MonoidHom.id F₃ := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i
  · show shiftAut (shiftAutInv a) = a
    rw [shiftAutInv_a, shiftAut_a]
  · show shiftAut (shiftAutInv b) = b
    rw [shiftAutInv_b, map_mul, map_mul, map_inv, shiftAut_b, shiftAut_c]
    group
  · show shiftAut (shiftAutInv c) = c
    rw [shiftAutInv_c, shiftAut_c]

/-- The shift, as an automorphism of `F₃`. -/
def shiftEquiv : F₃ ≃* F₃ where
  toFun := shiftAut
  invFun := shiftAutInv
  left_inv x := congrArg (fun f : F₃ →* F₃ => f x) shiftAutInv_comp_shiftAut
  right_inv x := congrArg (fun f : F₃ →* F₃ => f x) shiftAut_comp_shiftAutInv
  map_mul' := map_mul _

@[simp] theorem shiftEquiv_toMonoidHom : shiftEquiv.toMonoidHom = shiftAut := rfl

theorem shiftAut_injective : Function.Injective shiftAut := by
  intro x y hxy
  have hx := congrArg (fun f : F₃ →* F₃ => f x) shiftAutInv_comp_shiftAut
  have hy := congrArg (fun f : F₃ →* F₃ => f y) shiftAutInv_comp_shiftAut
  show x = y
  calc x = shiftAutInv (shiftAut x) := hx.symm
    _ = shiftAutInv (shiftAut y) := by rw [hxy]
    _ = y := hy

/-- **The automorphism moves the rows along.** -/
theorem shiftAut_rowElt (i : ℤ) : shiftAut (rowElt i) = rowElt (i + 1) := by
  unfold rowElt
  rw [map_mul, map_mul, map_zpow, map_zpow, shiftAut_b, shiftAut_c]
  rw [zpow_add, zpow_add, zpow_neg, zpow_neg, zpow_one, zpow_one]
  group

theorem shiftAut_comp_rowHom : shiftAut.comp rowHom = rowHom.comp shiftFree := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  show shiftAut (rowHom (FreeGroup.of i)) = rowHom (shiftFree (FreeGroup.of i))
  rw [rowHom_of, shiftFree_of, rowHom_of, shiftAut_rowElt]

theorem shiftAut_bElt (f : E) : shiftAut (bElt f) = bElt (shiftSeq f) := by
  unfold bElt
  rw [elt_shiftSeq]
  have h := congrArg (fun g : FreeGroup ℤ →* F₃ => g (elt f)) shiftAut_comp_rowHom
  exact h

theorem shiftAut_aElt (f : E) : shiftAut (aElt f) = aElt (shiftSeq f) := by
  unfold aElt
  rw [map_mul, map_mul, map_inv, shiftAut_a, shiftAut_bElt]

/-! ## 4.  The operation -/

/-- Higman's `σ`, as an operation on sets of sequences. -/
noncomputable def sigmaOp (B : Set E) : Set E := shiftSeq '' B

theorem ASub_sigmaOp (B : Set E) : ASub (sigmaOp B) = (ASub B).map shiftAut := by
  unfold ASub sigmaOp
  rw [MonoidHom.map_closure]
  congr 1
  refine Set.ext fun x => ?_
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨aElt f, ⟨f, hf, rfl⟩, shiftAut_aElt f⟩
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨shiftSeq f, ⟨f, hf, rfl⟩, (shiftAut_aElt f).symm⟩

/-- **Higman's operation `σ` preserves benignness.** -/
theorem benign_ASub_sigmaOp {B : Set E} (h : Benign (ASub B)) :
    Benign (ASub (sigmaOp B)) := by
  rw [ASub_sigmaOp]
  exact Benign.mapEmb h shiftAut shiftAut_injective

end Seq
end Higman
end GroupApproximation
