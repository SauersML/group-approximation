import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RefinementMatrix
import GroupApproximation.BooneHigman.SteinbergBasic.Kernel
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂` injectivity climbs one rank along the Leavitt refinement

Let `R` carry a Leavitt family, and let `r, k : Fin n` with `k ≠ r`.  The refinement
`D = refineHom L r : St_n(R) → St_{n+1}(R)` is onto (`refineHom_surjective`).  It is compatible
with elementary matrices through the vector refinement `refineVec L r`, which has the left
inverse `contractVec L r`.  So if `D w` has trivial matrix, then `stMat n w *ᵥ v = v` for every
`v`, and `w ∈ K₂(n, R)`.  Hence `K₂(n, R) = ⊥` implies `K₂(n + 1, R) = ⊥`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

open scoped Matrix
open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ} (r : Fin n)

theorem refine_mulVec_row {i j : Fin n} (hij : i ≠ j) (a : R) (hi : i = r) (v : Fin n → R) :
    stMat (n + 1) (refineHom L r (x i j hij a)) *ᵥ refineVec L r v =
      refineVec L r (stMat n (x i j hij a) *ᵥ v) := by
  have hj : ¬ j = r := fun h => hij (hi.trans h.symm)
  rw [refineHom_x, refineRoot_of_row L r hij a hi, map_mul, stMat_x, stMat_x, stMat_x,
    ← Matrix.mulVec_mulVec]
  funext t
  rcases Fin.eq_castSucc_or_eq_last t with ⟨k, rfl⟩ | rfl
  · by_cases hk : k = r
    · have hki : k = i := hk.trans hi.symm
      have hcki : Fin.castSucc k = Fin.castSucc i := congrArg Fin.castSucc hki
      rw [refine_mulVec_apply_eq hcki, refine_mulVec_apply_ne (Fin.castSucc_ne_last k),
        refine_mulVec_apply_ne (Fin.castSucc_ne_last j), refineVec_castSucc_of_eq L r v hk,
        refineVec_castSucc_of_ne L r v hj, refineVec_castSucc_of_eq L r _ hk,
        refine_mulVec_apply_eq hki, mul_add, mul_assoc]
    · have hki : k ≠ i := fun e => hk (e.trans hi)
      have hcki : Fin.castSucc k ≠ Fin.castSucc i := (Fin.castSucc_injective n).ne hki
      rw [refine_mulVec_apply_ne hcki, refine_mulVec_apply_ne (Fin.castSucc_ne_last k),
        refineVec_castSucc_of_ne L r v hk, refineVec_castSucc_of_ne L r _ hk,
        refine_mulVec_apply_ne hki]
  · have hlast : Fin.last n = Fin.last n := rfl
    rw [refine_mulVec_apply_ne (Fin.castSucc_ne_last i).symm, refine_mulVec_apply_eq hlast,
      refineVec_last L r v, refineVec_castSucc_of_ne L r v hj, refineVec_last L r _,
      refine_mulVec_apply_eq hi.symm, mul_add, mul_assoc]

theorem refine_mulVec_col {i j : Fin n} (hij : i ≠ j) (a : R) (hi : ¬ i = r) (hj : j = r)
    (v : Fin n → R) :
    stMat (n + 1) (refineHom L r (x i j hij a)) *ᵥ refineVec L r v =
      refineVec L r (stMat n (x i j hij a) *ᵥ v) := by
  rw [refineHom_x, refineRoot_of_col L r hij a hi hj, map_mul, stMat_x, stMat_x, stMat_x,
    ← Matrix.mulVec_mulVec]
  funext t
  rcases Fin.eq_castSucc_or_eq_last t with ⟨k, rfl⟩ | rfl
  · by_cases hk : k = r
    · have hki : k ≠ i := fun e => hi (e.symm.trans hk)
      have hcki : Fin.castSucc k ≠ Fin.castSucc i := (Fin.castSucc_injective n).ne hki
      rw [refine_mulVec_apply_ne hcki, refine_mulVec_apply_ne hcki,
        refineVec_castSucc_of_eq L r v hk, refineVec_castSucc_of_eq L r _ hk,
        refine_mulVec_apply_ne hki]
    · by_cases hki : k = i
      · have hcki : Fin.castSucc k = Fin.castSucc i := congrArg Fin.castSucc hki
        have hcji : Fin.castSucc j ≠ Fin.castSucc i := (Fin.castSucc_injective n).ne hij.symm
        rw [refine_mulVec_apply_eq hcki, refine_mulVec_apply_eq hcki,
          refine_mulVec_apply_ne hcji, refineVec_castSucc_of_ne L r v hk,
          refineVec_last L r v, refineVec_castSucc_of_eq L r v hj,
          refineVec_castSucc_of_ne L r _ hk, refine_mulVec_apply_eq hki, hj, add_assoc,
          refine_leavitt_split]
      · have hcki : Fin.castSucc k ≠ Fin.castSucc i := (Fin.castSucc_injective n).ne hki
        rw [refine_mulVec_apply_ne hcki, refine_mulVec_apply_ne hcki,
          refineVec_castSucc_of_ne L r v hk, refineVec_castSucc_of_ne L r _ hk,
          refine_mulVec_apply_ne hki]
  · have hri : r ≠ i := fun e => hi e.symm
    rw [refine_mulVec_apply_ne (Fin.castSucc_ne_last i).symm,
      refine_mulVec_apply_ne (Fin.castSucc_ne_last i).symm, refineVec_last L r v,
      refineVec_last L r _, refine_mulVec_apply_ne hri]

theorem refine_mulVec_x (i j : Fin n) (hij : i ≠ j) (a : R) (v : Fin n → R) :
    stMat (n + 1) (refineHom L r (x i j hij a)) *ᵥ refineVec L r v =
      refineVec L r (stMat n (x i j hij a) *ᵥ v) := by
  by_cases hi : i = r
  · exact refine_mulVec_row L r hij a hi v
  · by_cases hj : j = r
    · exact refine_mulVec_col L r hij a hi hj v
    · exact refine_mulVec_plain L r hij a hi hj v

theorem refine_mulVec (g : SteinbergGroup (Fin n) R) (v : Fin n → R) :
    stMat (n + 1) (refineHom L r g) *ᵥ refineVec L r v =
      refineVec L r (stMat n g *ᵥ v) := by
  have hg : g ∈ Subgroup.closure (Set.range
      (PresentedGroup.of : SteinbergGenerator (Fin n) R → SteinbergGroup (Fin n) R)) := by
    rw [PresentedGroup.closure_range_of]
    exact Subgroup.mem_top g
  revert v
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨⟨i, j, hij, a⟩, rfl⟩ := hy
      exact refine_mulVec_x L r i j hij a
  | one =>
      intro v
      simp only [map_one, Matrix.one_mulVec]
  | mul y z _ _ hy hz =>
      intro v
      simp only [map_mul]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz, hy]
  | inv y _ hy =>
      intro v
      have h1 := hy (stMat n y⁻¹ *ᵥ v)
      rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec] at h1
      rw [← h1, Matrix.mulVec_mulVec, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
        Matrix.one_mulVec]

/-- `K₂(n, R) = ⊥` implies `K₂(n + 1, R) = ⊥` for a ring with a Leavitt family, once `n ≥ 2`
(witnessed by two distinct indices `r` and `k`). -/
include L in
theorem K2_eq_bot_succ (k : Fin n) (hk : k ≠ r)
    (h : BooneHigman.SteinbergBasic.K2 (Fin n) R = ⊥) :
    BooneHigman.SteinbergBasic.K2 (Fin (n + 1)) R = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨w, rfl⟩ := refineHom_surjective L r k hk z
  rw [BooneHigman.SteinbergBasic.mem_K2_iff] at hz
  have hmat : stMat (n + 1) (refineHom L r w) = 1 := by
    have e := congrArg (fun e : elementaryGroup (Fin (n + 1)) R =>
      ((e : (Matrix (Fin (n + 1)) (Fin (n + 1)) R)ˣ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) hz
    exact e
  have hw : stMat n w = 1 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    have e := refine_mulVec L r w v
    rw [hmat, Matrix.one_mulVec] at e
    have e2 := congrArg (contractVec L r) e
    rw [contractVec_refineVec, contractVec_refineVec] at e2
    rw [Matrix.one_mulVec]
    exact e2.symm
  have hw' : w ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R := by
    rw [BooneHigman.SteinbergBasic.mem_K2_iff]
    exact Subtype.ext (Units.ext hw)
  rw [h, Subgroup.mem_bot] at hw'
  rw [hw', map_one]

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refine_mulVec_row
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refine_mulVec_col
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refine_mulVec_x
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refine_mulVec
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2_eq_bot_succ
