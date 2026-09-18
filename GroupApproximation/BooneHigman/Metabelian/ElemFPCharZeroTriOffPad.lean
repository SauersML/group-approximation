import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffFix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Undoing identity padding when the extra rows and columns are trivial (lane bh-met-90l)

For an index embedding `e : ι ↪ κ`, let `M : Matrix κ κ R` agree with the identity in every
row and every column outside the image of `e`.  Then `padHom e (M.submatrix e e) = M`
(`czTriOff_padHom_submatrix`).  Over a commutative ring, padding also preserves the
determinant (`czTriOff_det_padHom`).

We specialise to `e₀ = castSucc ∘ j.succAbove : Fin k ↪ Fin (k + 2)`
(`czTriOff_emb`).  Its image misses only `j.castSucc` and `last`.  So a matrix fixing both
basis vectors is the padding of its `e₀`-block (`czTriOff_padHom_of_fix`).

On the Steinberg side, `stab ∘ indexMap j.succAbove = indexMap e₀`, and the relabelling
`indexMap j.succAbove` lands in the root subgroup avoiding `j`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

/-- The complementary summand of `padEquiv` is the inclusion of the complement. -/
theorem czTriOff_padEquiv_inr {ι κ : Type*} (e : ι ↪ κ) (y : {a : κ // a ∉ Set.range e}) :
    ElementaryPadding.padEquiv e (Sum.inr y) = y.1 := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_padEquiv_inr

/-- A matrix that is the identity outside the `e`-block is the padding of that block. -/
theorem czTriOff_padHom_submatrix {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Ring R] (e : ι ↪ κ) (M : Matrix κ κ R)
    (h : ∀ a b : κ, (a ∉ Set.range e ∨ b ∉ Set.range e) → M a b = (1 : Matrix κ κ R) a b) :
    ElementaryPadding.padHom e (M.submatrix e e) = M := by
  ext a b
  obtain ⟨a', rfl⟩ := (ElementaryPadding.padEquiv e).surjective a
  obtain ⟨b', rfl⟩ := (ElementaryPadding.padEquiv e).surjective b
  rw [ElementaryPadding.padHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases a' with i | ⟨a, ha⟩ <;> rcases b' with i' | ⟨b, hb⟩
  · rw [Matrix.fromBlocks_apply₁₁, Matrix.submatrix_apply, ElementaryPadding.padEquiv_inl,
      ElementaryPadding.padEquiv_inl]
  · rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, ElementaryPadding.padEquiv_inl,
      czTriOff_padEquiv_inr, h (e i) b (Or.inr hb),
      Matrix.one_apply_ne (fun hab => hb (Set.mem_range.mpr ⟨i, hab⟩))]
  · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, ElementaryPadding.padEquiv_inl,
      czTriOff_padEquiv_inr, h a (e i') (Or.inl ha),
      Matrix.one_apply_ne (fun hab => ha (Set.mem_range.mpr ⟨i', hab.symm⟩))]
  · rw [Matrix.fromBlocks_apply₂₂, czTriOff_padEquiv_inr, czTriOff_padEquiv_inr,
      h a b (Or.inl ha)]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hab,
        Matrix.one_apply_ne (fun h' => hab (congrArg Subtype.val h'))]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_padHom_submatrix

/-- Identity padding preserves the determinant. -/
theorem czTriOff_det_padHom {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [CommRing R] (e : ι ↪ κ) (M : Matrix ι ι R) :
    (ElementaryPadding.padHom e M).det = M.det := by
  classical
  rw [ElementaryPadding.padHom_apply, Matrix.det_reindex_self]
  exact (Matrix.det_fromBlocks_zero₂₁ _ _ _).trans
    (by rw [Matrix.det_one, mul_one])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_det_padHom

/-- The embedding `castSucc ∘ j.succAbove : Fin k ↪ Fin (k + 2)`. -/
abbrev czTriOff_emb {k : ℕ} (j : Fin (k + 1)) : Fin k ↪ Fin (k + 1 + 1) :=
  (Fin.succAboveEmb j).trans Fin.castSuccEmb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_emb

theorem czTriOff_emb_apply {k : ℕ} (j : Fin (k + 1)) (z : Fin k) :
    czTriOff_emb j z = (j.succAbove z).castSucc := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_emb_apply

/-- The image of `czTriOff_emb j` misses only `j.castSucc` and `last`. -/
theorem czTriOff_eq_of_notMem_range {k : ℕ} {j : Fin (k + 1)} {a : Fin (k + 1 + 1)}
    (ha : a ∉ Set.range (czTriOff_emb j)) : a = j.castSucc ∨ a = Fin.last (k + 1) := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
  · left
    by_cases h : a' = j
    · rw [h]
    · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq h
      exact (ha (Set.mem_range.mpr ⟨z, by rw [czTriOff_emb_apply, hz]⟩)).elim
  · right
    rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_eq_of_notMem_range

/-- A matrix fixing `e_{j.castSucc}` and `e_last` is the padding of its `e₀`-block. -/
theorem czTriOff_padHom_of_fix {R : Type*} [Ring R] {k : ℕ} (j : Fin (k + 1))
    {D : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) R} (hj : czTriOff_Fix j.castSucc D)
    (hL : czTriOff_Fix (Fin.last (k + 1)) D) :
    ElementaryPadding.padHom (czTriOff_emb j)
      (D.submatrix (czTriOff_emb j) (czTriOff_emb j)) = D := by
  apply czTriOff_padHom_submatrix
  intro a b hab
  rcases hab with ha | hb
  · rcases czTriOff_eq_of_notMem_range ha with rfl | rfl
    · exact czTriOff_fix_row hj b
    · exact czTriOff_fix_row hL b
  · rcases czTriOff_eq_of_notMem_range hb with rfl | rfl
    · exact czTriOff_fix_col hj a
    · exact czTriOff_fix_col hL a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_padHom_of_fix

/-- `stab ∘ indexMap j.succAbove = indexMap e₀`. -/
theorem czTriOff_stab_indexMap {R : Type*} [Ring R] {k : ℕ} (j : Fin (k + 1)) (g : St k R) :
    stab (k + 1) R (indexMap (Fin.succAboveEmb j) g) = indexMap (czTriOff_emb j) g := by
  show indexMap Fin.castSuccEmb (indexMap (Fin.succAboveEmb j) g) =
    indexMap ((Fin.succAboveEmb j).trans Fin.castSuccEmb) g
  rw [indexMap_trans]
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_stab_indexMap

/-- Relabelling along `j.succAbove` lands in the root subgroup avoiding `j`. -/
theorem czTriOff_indexMap_mem_off {R : Type*} [Ring R] {k : ℕ} (j : Fin (k + 1))
    (g : St k R) : indexMap (Fin.succAboveEmb j) g ∈ czStabGen_off R j := by
  have hg := mem_closure_range_of (R := R) g
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨⟨p, q, hpq, a⟩, rfl⟩ := hg
    change indexMap (Fin.succAboveEmb j) (x p q hpq a) ∈ czStabGen_off R j
    rw [indexMap_x]
    exact Subgroup.subset_closure ⟨j.succAbove p, j.succAbove q,
      (Fin.succAboveEmb j).injective.ne hpq, a, Fin.succAbove_ne j p, Fin.succAbove_ne j q, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul g h _ _ ihg ihh => rw [map_mul]; exact mul_mem ihg ihh
  | inv g _ ih => rw [map_inv]; exact inv_mem ih

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_indexMap_mem_off

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
