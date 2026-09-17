import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RefinementKernel
import GroupApproximation.Meta.AxiomGuard

/-!
# The Leavitt refinement carries `K₂(n, R)` exactly onto `K₂(n + 1, R)`

Let `R` carry a Leavitt family `s₀, s₁, t₀, t₁`, let `r, k : Fin n` with `k ≠ r`, and let
`D = refineHom L r : St_n(R) → St_{n+1}(R)`.  `LeavittFP.K2RefinementKernel` shows that
`D w ∈ K₂(n + 1)` forces `w ∈ K₂(n)`.  This file adds the converse and its consequences.

* `refineVec L r : R^n → R^{n+1}` and `contractVec L r` are mutually inverse:
  `contractVec ∘ refineVec = id` is `contractVec_refineVec`, and `refineVec ∘ contractVec = id`
  (`refineVec_contractVec`) uses `t₀ s₀ = t₁ s₁ = 1` and `t₀ s₁ = t₁ s₀ = 0`.
* So if `stMat n w = 1`, then `stMat (n + 1) (D w)` fixes every `refineVec v`, hence every vector,
  and `D w ∈ K₂(n + 1)` (`refineHom_mem_K2`).
* With surjectivity of `D` this gives `K₂(n + 1, R) = D(K₂(n, R))` (`K2_map_refineHom`).
* A surjective image of a finitely normally generated subgroup is finitely normally generated, so
  finite normal generation of `K₂` climbs one rank (`K2_isFinitelyNormallyGenerated_succ`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ} (r : Fin n)

/-- `refineVec L r` is a right inverse of `contractVec L r`. -/
theorem refineVec_contractVec (w : Fin (n + 1) → R) : refineVec L r (contractVec L r w) = w := by
  funext p
  rcases Fin.eq_castSucc_or_eq_last p with ⟨k, rfl⟩ | rfl
  · by_cases hk : k = r
    · rw [refineVec_castSucc_of_eq L r _ hk, contractVec, if_pos hk, mul_add, ← mul_assoc,
        ← mul_assoc, L.t0_s0, L.t0_s1, one_mul, zero_mul, add_zero]
    · rw [refineVec_castSucc_of_ne L r _ hk, contractVec, if_neg hk]
  · rw [refineVec_last L r _, contractVec, if_pos (rfl : r = r), mul_add, ← mul_assoc,
      ← mul_assoc, L.t1_s0, L.t1_s1, zero_mul, one_mul, zero_add]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineVec_contractVec

/-- The refinement of a `K₂` element is a `K₂` element. -/
theorem refineHom_mem_K2 {w : SteinbergGroup (Fin n) R}
    (hw : w ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R) :
    refineHom L r w ∈ BooneHigman.SteinbergBasic.K2 (Fin (n + 1)) R := by
  rw [BooneHigman.SteinbergBasic.mem_K2_iff] at hw ⊢
  have hmat : stMat n w = 1 := by
    have e := congrArg (fun e : elementaryGroup (Fin n) R =>
      ((e : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)) hw
    exact e
  have hD : stMat (n + 1) (refineHom L r w) = 1 := by
    rw [Matrix.ext_iff_mulVec]
    intro u
    have e := refine_mulVec L r w (contractVec L r u)
    rw [hmat, Matrix.one_mulVec, refineVec_contractVec] at e
    rw [Matrix.one_mulVec]
    exact e
  exact Subtype.ext (Units.ext hD)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineHom_mem_K2

/-- An element whose refinement lies in `K₂(n + 1)` lies in `K₂(n)`. -/
theorem mem_K2_of_refineHom_mem {w : SteinbergGroup (Fin n) R}
    (hz : refineHom L r w ∈ BooneHigman.SteinbergBasic.K2 (Fin (n + 1)) R) :
    w ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R := by
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
  rw [BooneHigman.SteinbergBasic.mem_K2_iff]
  exact Subtype.ext (Units.ext hw)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.mem_K2_of_refineHom_mem

/-- `K₂(n + 1, R)` is exactly the image of `K₂(n, R)` under the Leavitt refinement. -/
theorem K2_map_refineHom (k : Fin n) (hk : k ≠ r) :
    (BooneHigman.SteinbergBasic.K2 (Fin n) R).map (refineHom L r) =
      BooneHigman.SteinbergBasic.K2 (Fin (n + 1)) R := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro w hw
    exact refineHom_mem_K2 L r hw
  · intro z hz
    obtain ⟨w, rfl⟩ := refineHom_surjective L r k hk z
    exact Subgroup.mem_map_of_mem (refineHom L r) (mem_K2_of_refineHom_mem L r hz)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2_map_refineHom

/-- Finite normal generation of `K₂` climbs one rank along the Leavitt refinement. -/
theorem K2_isFinitelyNormallyGenerated_succ (k : Fin n) (hk : k ≠ r)
    (h : (BooneHigman.SteinbergBasic.K2 (Fin n) R).IsFinitelyNormallyGenerated) :
    (BooneHigman.SteinbergBasic.K2 (Fin (n + 1)) R).IsFinitelyNormallyGenerated := by
  rw [← K2_map_refineHom L r k hk]
  exact h.map (refineHom_surjective L r k hk)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2_isFinitelyNormallyGenerated_succ

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP
