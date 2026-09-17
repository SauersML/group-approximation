import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RefinementSurjective
import GroupApproximation.Meta.AxiomGuard

/-!
# Matrix compatibility of the Leavitt refinement

`stMat n : St_n(R) →* M_n(R)` sends a Steinberg element to its elementary matrix.  The refinement
of column vectors `refineVec L r : R^n → R^{n+1}` keeps the coordinates `k ≠ r`.  It sends the
coordinate `v r` to the pair `(t₀ v r, t₁ v r)` in the slots `castSucc r` and `last n`.
The map `contractVec L r` recombines those two slots as `s₀ w₁ + s₁ w₂`, so it is a left inverse.

On each generator, `stMat (n + 1) (refineHom L r g) *ᵥ refineVec v = refineVec (stMat n g *ᵥ v)`.
This file checks that identity coordinate by coordinate.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

open scoped Matrix
open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ} (r : Fin n)

/-- The elementary matrix of a Steinberg element. -/
def stMat (n : ℕ) : SteinbergGroup (Fin n) R →* Matrix (Fin n) (Fin n) R :=
  (Units.coeHom _).comp ((elementaryGroup (Fin n) R).subtype.comp projection)

theorem stMat_x (i j : Fin n) (hij : i ≠ j) (a : R) :
    stMat n (x i j hij a) = 1 + Matrix.single i j a := by
  have e : ((projection (x i j hij a) : elementaryGroup (Fin n) R) :
      (Matrix (Fin n) (Fin n) R)ˣ) = elementaryUnit i j hij a := by
    rw [projection_x, elementaryRoot_val]
  exact congrArg Units.val e

/-- Refine a vector along the split index `r`. -/
def refineVec (v : Fin n → R) (p : Fin (n + 1)) : R :=
  Fin.lastCases (motive := fun _ => R) (L.t1 * v r)
    (fun i => if i = r then L.t0 * v i else v i) p

/-- Recombine the two halves of the split index `r`. -/
def contractVec (w : Fin (n + 1) → R) (k : Fin n) : R :=
  if k = r then L.s0 * w (Fin.castSucc k) + L.s1 * w (Fin.last n) else w (Fin.castSucc k)

theorem refineVec_last (v : Fin n → R) : refineVec L r v (Fin.last n) = L.t1 * v r := by
  simp only [refineVec, Fin.lastCases_last]

theorem refineVec_castSucc_of_eq (v : Fin n → R) {k : Fin n} (hk : k = r) :
    refineVec L r v (Fin.castSucc k) = L.t0 * v k := by
  simp only [refineVec, Fin.lastCases_castSucc, if_pos hk]

theorem refineVec_castSucc_of_ne (v : Fin n → R) {k : Fin n} (hk : ¬ k = r) :
    refineVec L r v (Fin.castSucc k) = v k := by
  simp only [refineVec, Fin.lastCases_castSucc, if_neg hk]

theorem contractVec_refineVec (v : Fin n → R) : contractVec L r (refineVec L r v) = v := by
  funext k
  by_cases hk : k = r
  · rw [contractVec, if_pos hk, refineVec_castSucc_of_eq L r v hk, refineVec_last,
      ← mul_assoc, ← mul_assoc, hk, ← add_mul, L.sum_range, one_mul]
  · rw [contractVec, if_neg hk, refineVec_castSucc_of_ne L r v hk]

/-- The Leavitt identity `a s₁ t₁ b + a s₀ t₀ b = a b`. -/
theorem refine_leavitt_split (a b : R) :
    a * L.s1 * (L.t1 * b) + a * L.s0 * (L.t0 * b) = a * b := by
  calc a * L.s1 * (L.t1 * b) + a * L.s0 * (L.t0 * b)
      = a * (L.s1 * L.t1) * b + a * (L.s0 * L.t0) * b := by simp only [mul_assoc]
    _ = a * (L.s0 * L.t0 + L.s1 * L.t1) * b := by
      rw [add_comm (L.s0 * L.t0), mul_add, add_mul]
    _ = a * b := by rw [L.sum_range, mul_one]

theorem refine_mulVec_apply_eq {m : Type*} [Fintype m] [DecidableEq m] {p q t : m} {c : R}
    {w : m → R} (h : t = p) : ((1 + Matrix.single p q c) *ᵥ w) t = w t + c * w q := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply,
    Function.update_apply, if_pos h]

theorem refine_mulVec_apply_ne {m : Type*} [Fintype m] [DecidableEq m] {p q t : m} {c : R}
    {w : m → R} (h : t ≠ p) : ((1 + Matrix.single p q c) *ᵥ w) t = w t := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply,
    Function.update_apply, if_neg h, Pi.zero_apply, add_zero]

theorem refine_mulVec_plain {i j : Fin n} (hij : i ≠ j) (a : R) (hi : ¬ i = r) (hj : ¬ j = r)
    (v : Fin n → R) :
    stMat (n + 1) (refineHom L r (x i j hij a)) *ᵥ refineVec L r v =
      refineVec L r (stMat n (x i j hij a) *ᵥ v) := by
  rw [refineHom_x, refineRoot_of_plain L r hij a hi hj, stMat_x, stMat_x]
  funext t
  rcases Fin.eq_castSucc_or_eq_last t with ⟨k, rfl⟩ | rfl
  · by_cases hk : k = r
    · have hki : k ≠ i := fun e => hi (e.symm.trans hk)
      have hcki : Fin.castSucc k ≠ Fin.castSucc i := (Fin.castSucc_injective n).ne hki
      rw [refine_mulVec_apply_ne hcki, refineVec_castSucc_of_eq L r v hk,
        refineVec_castSucc_of_eq L r _ hk, refine_mulVec_apply_ne hki]
    · by_cases hki : k = i
      · have hcki : Fin.castSucc k = Fin.castSucc i := congrArg Fin.castSucc hki
        rw [refine_mulVec_apply_eq hcki, refineVec_castSucc_of_ne L r v hk,
          refineVec_castSucc_of_ne L r v hj, refineVec_castSucc_of_ne L r _ hk,
          refine_mulVec_apply_eq hki]
      · have hcki : Fin.castSucc k ≠ Fin.castSucc i := (Fin.castSucc_injective n).ne hki
        rw [refine_mulVec_apply_ne hcki, refineVec_castSucc_of_ne L r v hk,
          refineVec_castSucc_of_ne L r _ hk, refine_mulVec_apply_ne hki]
  · have hri : r ≠ i := fun e => hi e.symm
    rw [refine_mulVec_apply_ne (Fin.castSucc_ne_last i).symm, refineVec_last L r v,
      refineVec_last L r _, refine_mulVec_apply_ne hri]

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.stMat
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.stMat_x
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineVec
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.contractVec
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineVec_last
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineVec_castSucc_of_eq
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineVec_castSucc_of_ne
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.contractVec_refineVec
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refine_leavitt_split
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refine_mulVec_apply_eq
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refine_mulVec_apply_ne
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refine_mulVec_plain
