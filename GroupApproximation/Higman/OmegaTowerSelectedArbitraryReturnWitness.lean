import GroupApproximation.Higman.OmegaTowerSelectedRowWord

/-!
# Selected return witnesses with an arbitrary row index

The static-seam boundary only says that a translated canonical label returns
to some row label, whose index is initially an arbitrary element of `K`.
This file retains that index and reifies its unique row-basis spelling.  The
normal-form classifier can then prove that this spelling is canonical rather
than assuming that conclusion at its input.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open Monoid

/-- The row-basis word carried by a selected signed block word. -/
noncomputable def selectedRowIndexInvHom (m : ℕ) (B : Set E) :
    FreeGroup (SelectedBlock m B) →* FreeGroup ℤ :=
  FreeGroup.lift fun beta => (elt (beta : E))⁻¹

/-- Embed a row-basis word into the conjugating subgroup `K`. -/
def rowKHom : FreeGroup ℤ →* ↥Conj.K :=
  rowHom.codRestrict Conj.K fun w => rowHom_mem_K w

@[simp] theorem rowKHom_elt (f : E) : rowKHom (elt f) = bK f := rfl

theorem rowKHom_comp_selectedRowIndexInvHom (m : ℕ) (B : Set E) :
    rowKHom.comp (selectedRowIndexInvHom m B) =
      selectedRowInvHom m B := by
  refine FreeGroup.ext_hom _ _ fun beta => ?_
  apply Subtype.ext
  simp [rowKHom, selectedRowIndexInvHom, selectedRowInvHom_of, bK, bElt]

/-- The row-basis spelling of the arbitrary returning index, reconstructed
from the selected row word and the canonical source index. -/
noncomputable def selectedReturnRowWord
    (m : ℕ) (B : Set E) (v : FreeGroup (SelectedBlock m B)) (l : E) :
    FreeGroup ℤ :=
  (selectedRowIndexInvHom m B v)⁻¹ * elt l

theorem rowKHom_selectedReturnRowWord_eq
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    {l : E} {q : ↥Conj.K}
    (hRow : selectedRowInvHom m B v = bK l * q⁻¹) :
    rowKHom (selectedReturnRowWord m B v l) = q := by
  have hselected := DFunLike.congr_fun
    (rowKHom_comp_selectedRowIndexInvHom m B) v
  rw [MonoidHom.comp_apply] at hselected
  rw [selectedReturnRowWord, map_mul, map_inv, hselected, rowKHom_elt, hRow]
  group

/-- Generic row-label return criterion, without assuming the target index is
the ordered word of a sequence. -/
theorem rightLabel_rowLabelK_eq_iff_link
    (m : ℕ) (g : Cent3 (rowOut m)) (l : E) (q : ↥Conj.K) :
    CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) g
          (slimRowLabel m (bK l)) = slimRowLabel m q ↔
      slimBaseCode m l * g * (slimKBase m q)⁻¹ ∈ slimLink m := by
  unfold slimRowLabel
  rw [CentralHNNFreeLabel.rightLabel_labelOf]
  change (((slimTransversal m).compl (1 : ℤˣ)).equiv
      (slimKBase m (bK l) * g)).2 =
        (((slimTransversal m).compl (1 : ℤˣ)).equiv
          (slimKBase m q)).2 ↔ _
  rw [slimKBase_bK]
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using
    (FiniteHNNFreeLabelAction.source_transversal_eq_iff
      (A := slimLink m) (B := slimLink m) (slimTransversal m)
      (slimBaseCode m l * g * (slimKBase m q)⁻¹)
      (slimKBase m q))

/-- A generic row-label return has one literal selected block spelling and
an exact intrinsic endpoint equation in `K`. -/
theorem exists_selected_orbit_word_of_rightLabel_rowLabelK_eq
    {m : ℕ} {B : Set E} {g : Cent3 (rowOut m)} {l : E} {q : ↥Conj.K}
    (hg : g ∈ slimGenSub m B)
    (hlabel : CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) g
          (slimRowLabel m (bK l)) = slimRowLabel m q) :
    ∃ v : FreeGroup (SelectedBlock m B),
      selectedCodeHom m B v = g ∧
      selectedLinkHom m B v =
        slimBaseCode m l * g * (slimKBase m q)⁻¹ ∧
      selectedRowInvHom m B v = bK l * q⁻¹ := by
  have hlink := (rightLabel_rowLabelK_eq_iff_link m g l q).mp hlabel
  rw [← slimLinkLift_range m] at hlink
  obtain ⟨u, hu⟩ := hlink
  have hcode : blockAHom m u = genProjection3 m g := by
    rw [← genProjection3_comp_slimLinkLift m, MonoidHom.comp_apply, hu]
    simp only [map_mul, map_inv, genProjection3_emb3, slimBaseCode,
      slimKBase, MonoidHom.comp_apply, inv_one, mul_one,
      one_mul]
  have hselected :
      u ∈ Subgroup.closure (FreeGroup.of '' selectedBlocks m B) :=
    mem_closure_selectedBlocks_of_blockAHom_mem
      (by rw [hcode]; exact genProjection3_mem_ASub_of_mem_slimGenSub hg)
  have huRange : u ∈ (FreeGroup.map (selectedBlockIncl m B)).range := by
    rwa [selectedBlockInclMap_range]
  obtain ⟨v, rfl⟩ := huRange
  have hrow : selectedRowInvHom m B v = bK l * q⁻¹ := by
    change blockKInvHom m (FreeGroup.map (selectedBlockIncl m B) v) = _
    apply Subtype.ext
    have hmap := DFunLike.congr_fun (Ksubtype_comp_blockKInvHom m)
      (FreeGroup.map (selectedBlockIncl m B) v)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hmap
    change ((blockKInvHom m
        (FreeGroup.map (selectedBlockIncl m B) v) : ↥Conj.K) : F₃) =
      rowIntoF3 (blockRowInvHom m
        (FreeGroup.map (selectedBlockIncl m B) v)) at hmap
    change ((blockKInvHom m
      (FreeGroup.map (selectedBlockIncl m B) v) : ↥Conj.K) : F₃) = _
    rw [hmap]
    have hbase : blockRowInvHom m
        (FreeGroup.map (selectedBlockIncl m B) v) =
        Row.basisHom (elt l) * (Seq.retract (q : F₃))⁻¹ := by
      rw [← baseRet3_comp_slimLinkLift m, MonoidHom.comp_apply, hu]
      simp only [map_mul, map_inv, baseRet3_emb3, slimBaseCode,
        baseRet3_eq_one_of_mem_slimGenSub hg, mul_one, slimKBase,
        MonoidHom.comp_apply]
      rfl
    rw [hbase, map_mul, map_inv]
    have hl := DFunLike.congr_fun rowIntoF3_comp_basisHom (elt l)
    change rowIntoF3 (Row.basisHom (elt l)) = rowHom (elt l) at hl
    rw [hl, rowIntoF3_retract_coe_K]
    rfl
  refine ⟨v, ?_, hu, hrow⟩
  rw [selectedCodeHom, MonoidHom.comp_apply,
    selectedAHom_eq_blockAHom_comp, MonoidHom.comp_apply, hcode]
  exact genHom_genProjection3_eq_of_mem_slimGenSub hg

@[simp] theorem indexCanonical3_indexEmb3_eq_slimKBase_rowKHom
    (m : ℕ) (w : FreeGroup ℤ) :
    indexCanonical3 m (indexEmb3 m w) = slimKBase m (rowKHom w) := by
  rw [indexCanonical3_indexEmb3]
  change emb3 (rowOut m) (Row.basisHom w) =
    emb3 (rowOut m) (Seq.retract (rowHom w))
  have hretract := DFunLike.congr_fun retract_comp_rowHom w
  rw [MonoidHom.comp_apply] at hretract
  rw [hretract]

@[simp] theorem lowStableProjection3_indexEmb3
    (m : ℕ) (w : FreeGroup ℤ) :
    lowStableProjection3 m (indexEmb3 m w) = lowRowProjection m w := by
  simp [indexEmb3, indexEmb2, indexEmb1]

/-- The applied form of `lowStableProjection3_comp_genHom`.  The composite
equation cannot fire under `simp`, which only ever sees the projection
already applied to an index code. -/
theorem lowStableProjection3_indexGenHom (m : ℕ) (x : F₃) :
    lowStableProjection3 m (indexGenHom m x) = stableFreeHom m x := by
  have h := DFunLike.congr_fun (lowStableProjection3_comp_genHom m) x
  rw [MonoidHom.comp_apply] at h
  exact h

/-- The full arbitrary-row return witness in the binary indexed free
product.  Its right factor is the explicit reconstructed row-basis word. -/
theorem exists_selected_arbitrary_indexed_return_witness
    {m : ℕ} {B : Set E} {g : Cent3 (rowOut m)} {l : E} {q : ↥Conj.K}
    (hg : g ∈ slimGenSub m B)
    (hlabel : CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) g
          (slimRowLabel m (bK l)) = slimRowLabel m q) :
    ∃ v : FreeGroup (SelectedBlock m B),
      let w := selectedReturnRowWord m B v l
      rowKHom w = q ∧
      selectedIndexedLinkHom m B v =
        CoprodI.of (i := false) (lowRowFactor m (elt l)) *
          CoprodI.of (i := true) (selectedAHom m B v) *
            (CoprodI.of (i := false) (lowRowFactor m w))⁻¹ ∧
      selectedRowInvHom m B v = bK l * q⁻¹ := by
  obtain ⟨v, hvCode, hvLink, hvRow⟩ :=
    exists_selected_orbit_word_of_rightLabel_rowLabelK_eq hg hlabel
  let w := selectedReturnRowWord m B v l
  have hwq : rowKHom w = q :=
    rowKHom_selectedReturnRowWord_eq hvRow
  have hindex : selectedIndexLinkHom m B v =
      indexBaseCode m l * selectedIndexCodeHom m B v *
        (indexEmb3 m w)⁻¹ := by
    apply indexCanonical3_injective m
    rw [← MonoidHom.comp_apply,
      indexCanonical3_comp_selectedIndexLinkHom,
      map_mul, map_mul, map_inv, indexCanonical3_indexBaseCode,
      ← MonoidHom.comp_apply, indexCanonical3_comp_selectedIndexCodeHom,
      indexCanonical3_indexEmb3_eq_slimKBase_rowKHom, hwq,
      hvCode]
    exact hvLink
  have hproject := congrArg
    ((lowStableToIndexed m).comp (lowStableProjection3 m)) hindex
  have hindexed : selectedIndexedLinkHom m B v =
      CoprodI.of (i := false) (lowRowFactor m (elt l)) *
        CoprodI.of (i := true) (selectedAHom m B v) *
          (CoprodI.of (i := false) (lowRowFactor m w))⁻¹ := by
    change selectedIndexedLinkHom m B v = _ at hproject
    simpa only [map_mul, map_inv, lowStableProjection3_indexBaseCode,
      lowStableToIndexed_lowRowProjection, selectedIndexCodeHom,
      MonoidHom.comp_apply, lowStableProjection3_indexGenHom,
      lowStableToIndexed_stableFreeHom, lowStableProjection3_indexEmb3]
      using hproject
  exact ⟨v, hwq, hindexed, hvRow⟩

end Omega
end Higman
end GroupApproximation
