import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RefinementDescend
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjectivity of the Leavitt refinement homomorphism

If `n` has an index `k ≠ r`, then `refineHom L r : St_n(R) → St_{n+1}(R)` is onto.
Root elements that do not involve both halves `castSucc r` and `last n` of the split index are
images of single generators, because `tᵢ sⱼ = δᵢⱼ`:

* `x_{r j}(c) = D x_{r j}(s₀ c)` and `x_{last, j}(c) = D x_{r j}(s₁ c)` for `j ≠ r`;
* `x_{i r}(c) = D x_{i r}(c t₀)` and `x_{i, last}(c) = D x_{i r}(c t₁)` for `i ≠ r`;
* `x_{i j}(c) = D x_{i j}(c)` if `i, j ≠ r`.

The two remaining roots are commutators through the spare index `k`:
`x_{last, r}(c) = ⁅x_{last, k}(c), x_{k r}(1)⁆` and `x_{r, last}(c) = ⁅x_{r k}(c), x_{k, last}(1)⁆`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ} (r : Fin n)

theorem refine_mem_range_cast_cast (i j : Fin n) (h : Fin.castSucc i ≠ Fin.castSucc j) (c : R) :
    x (Fin.castSucc i) (Fin.castSucc j) h c ∈ (refineHom L r).range := by
  have hij : i ≠ j := fun e => h (congrArg Fin.castSucc e)
  by_cases hi : i = r
  · exact MonoidHom.mem_range.mpr ⟨x i j hij (L.s0 * c), by
      rw [refineHom_x, refineRoot_of_row L r hij _ hi, ← mul_assoc, ← mul_assoc, L.t0_s0,
        L.t1_s0, one_mul, zero_mul, x_zero, mul_one]⟩
  · by_cases hj : j = r
    · exact MonoidHom.mem_range.mpr ⟨x i j hij (c * L.t0), by
        rw [refineHom_x, refineRoot_of_col L r hij _ hi hj, mul_assoc, mul_assoc, L.t0_s0,
          L.t0_s1, mul_one, mul_zero, x_zero, mul_one]⟩
    · exact MonoidHom.mem_range.mpr ⟨x i j hij c, by
        rw [refineHom_x, refineRoot_of_plain L r hij c hi hj]⟩

theorem refine_mem_range_last_cast (j : Fin n) (h : Fin.last n ≠ Fin.castSucc j) (c : R)
    (hj : ¬ j = r) : x (Fin.last n) (Fin.castSucc j) h c ∈ (refineHom L r).range := by
  have hrj : r ≠ j := fun e => hj e.symm
  exact MonoidHom.mem_range.mpr ⟨x r j hrj (L.s1 * c), by
    rw [refineHom_x, refineRoot_of_row L r hrj _ rfl, ← mul_assoc, ← mul_assoc, L.t0_s1,
      L.t1_s1, zero_mul, one_mul, x_zero, one_mul]⟩

theorem refine_mem_range_cast_last (i : Fin n) (h : Fin.castSucc i ≠ Fin.last n) (c : R)
    (hi : ¬ i = r) : x (Fin.castSucc i) (Fin.last n) h c ∈ (refineHom L r).range := by
  have hir : i ≠ r := hi
  exact MonoidHom.mem_range.mpr ⟨x i r hir (c * L.t1), by
    rw [refineHom_x, refineRoot_of_col L r hir _ hi rfl, mul_assoc, mul_assoc, L.t1_s0,
      L.t1_s1, mul_zero, mul_one, x_zero, one_mul]⟩

theorem refine_mem_range_last (k : Fin n) (hk : k ≠ r) (j : Fin n)
    (h : Fin.last n ≠ Fin.castSucc j) (c : R) :
    x (Fin.last n) (Fin.castSucc j) h c ∈ (refineHom L r).range := by
  by_cases hj : j = r
  · have hkj : k ≠ j := fun e => hk (e.trans hj)
    have e := x_commutator (Fin.last n) (Fin.castSucc k) (Fin.castSucc j)
      (Fin.castSucc_ne_last k).symm ((Fin.castSucc_injective n).ne hkj) h c 1
    rw [mul_one] at e
    rw [← e, commutatorElement_def]
    have ha := refine_mem_range_last_cast L r k (Fin.castSucc_ne_last k).symm c hk
    have hb := refine_mem_range_cast_cast L r k j ((Fin.castSucc_injective n).ne hkj) 1
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · exact refine_mem_range_last_cast L r j h c hj

theorem refine_mem_range_to_last (k : Fin n) (hk : k ≠ r) (i : Fin n)
    (h : Fin.castSucc i ≠ Fin.last n) (c : R) :
    x (Fin.castSucc i) (Fin.last n) h c ∈ (refineHom L r).range := by
  by_cases hi : i = r
  · have hik : i ≠ k := fun e => hk (e.symm.trans hi)
    have e := x_commutator (Fin.castSucc i) (Fin.castSucc k) (Fin.last n)
      ((Fin.castSucc_injective n).ne hik) (Fin.castSucc_ne_last k) h c 1
    rw [mul_one] at e
    rw [← e, commutatorElement_def]
    have ha := refine_mem_range_cast_cast L r i k ((Fin.castSucc_injective n).ne hik) c
    have hb := refine_mem_range_cast_last L r k (Fin.castSucc_ne_last k) 1 hk
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · exact refine_mem_range_cast_last L r i h c hi

theorem refine_x_mem_range (k : Fin n) (hk : k ≠ r) (p q : Fin (n + 1)) (hpq : p ≠ q)
    (c : R) : x p q hpq c ∈ (refineHom L r).range := by
  rcases Fin.eq_castSucc_or_eq_last p with ⟨i, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last q with ⟨j, rfl⟩ | rfl
    · exact refine_mem_range_cast_cast L r i j hpq c
    · exact refine_mem_range_to_last L r k hk i hpq c
  · rcases Fin.eq_castSucc_or_eq_last q with ⟨j, rfl⟩ | rfl
    · exact refine_mem_range_last L r k hk j hpq c
    · exact absurd rfl hpq

/-- The refinement homomorphism is onto once there is a spare index `k ≠ r`. -/
theorem refineHom_surjective (k : Fin n) (hk : k ≠ r) : Function.Surjective (refineHom L r) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  intro g _
  refine PresentedGroup.generated_by _ (refineHom L r).range ?_ g
  rintro ⟨p, q, hpq, c⟩
  exact refine_x_mem_range L r k hk p q hpq c

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineHom_surjective
