import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulXaConj
import Mathlib.Algebra.Group.Subgroup.Pointwise
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev's Lemma 1.3(b) for all of `St_r(A)`

Continuing `TulXaConj`. Let `|I| ≥ 5`, `a = u_a v` and `b = u_b v`, with `w ⊥ v`. Then:
* `Xa_conj_x`: `x_ij(t) X_{v,bw}(a) x_ij(-t) = X_{x_ij(t) v, b w x_ij(-t)}(a)`. The canonical
  pieces of `b w` are conjugated one at a time (`tx_conj_x`), and the result is reassembled with
  `Xa_eq_prod`.
* **`Xa_conj` (T 1.3(b))**: `α X_{v,bw}(a) α⁻¹ = X_{αv, bwα⁻¹}(a)` for every `α ∈ St(A)`, by
  induction on words in the generators. At each step `b = (u_b π(α)⁻¹)(π(α) v)` and
  `a = (u_a π(α)⁻¹)(π(α) v)`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace TulElem

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (Elements)

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A] (hX : Elements I A)
  [Fact (IsLocal hX)]

/-- Conjugation carries a product in `Cv v` to the product of the conjugates in `Cv v'`. -/
theorem conj_prod (y : SteinbergGroup I A) {v v' : I → A} {ι : Type*} (s : Finset ι)
    (F : ι → Cv hX v) (G : ι → Cv hX v')
    (h : ∀ k, y * (F k : SteinbergGroup I A) * y⁻¹ = G k) :
    y * ((∏ k ∈ s, F k : Cv hX v) : SteinbergGroup I A) * y⁻¹ =
      ((∏ k ∈ s, G k : Cv hX v') : SteinbergGroup I A) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Subgroup.coe_mul, Subgroup.coe_mul, ← h a,
      ← ih]
    group

#audit_axioms conj_prod

/-- T 1.3(b) for a generator `x_ij(t)`. -/
theorem Xa_conj_x (h5 : 5 ≤ Fintype.card I) {i j : I} (hij : i ≠ j) (t : A) {v w : I → A}
    (ua ub : I → A) (hw : w ⬝ᵥ v = 0) :
    x i j hij t * Xa hX (Nat.le_of_succ_le h5) v ((ub ⬝ᵥ v) • w) ua * (x i j hij t)⁻¹ =
      Xa hX (Nat.le_of_succ_le h5) (pm (x i j hij t) *ᵥ v)
        ((ub ⬝ᵥ v) • (w ᵥ* pm (x i j hij t)⁻¹)) (ua ᵥ* pm (x i j hij t)⁻¹) := by
  have h4 : 4 ≤ Fintype.card I := Nat.le_of_succ_le h5
  have hv' : ∀ pq : I × I,
      (pc v w ub pq.1 pq.2 ᵥ* pm (x i j hij t)⁻¹) ⬝ᵥ (pm (x i j hij t) *ᵥ v) = 0 := fun pq => by
    rw [dot_transform, pc_dot]
  have h2' : ∀ pq : I × I, TwoZ (pc v w ub pq.1 pq.2 ᵥ* pm (x i j hij t)⁻¹) := by
    intro pq
    obtain ⟨l, m, hlm, hl, hm⟩ := exists_two_not_mem [pq.1, pq.2, j]
      (by simp only [List.length_cons, List.length_nil]; omega)
    simp at hl hm
    refine ⟨l, m, hlm, ?_, ?_⟩
    · rw [vecMul_pm_x_inv, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hl.2.2, smul_zero,
        sub_zero, pc_apply_of_ne v w ub hl.1 hl.2.1]
    · rw [vecMul_pm_x_inv, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hm.2.2, smul_zero,
        sub_zero, pc_apply_of_ne v w ub hm.1 hm.2.1]
  have hsum : (ub ⬝ᵥ v) • (w ᵥ* pm (x i j hij t)⁻¹) =
      ∑ pq : I × I, pc v w ub pq.1 pq.2 ᵥ* pm (x i j hij t)⁻¹ := by
    rw [← smul_vecMul, ← pc_sum_all ub hw, sum_vecMul]
  rw [Xa_pieces hX h4 ua ub hw, hsum, Xa_eq_prod hX h4 (pm (x i j hij t) *ᵥ v)
    (ua ᵥ* pm (x i j hij t)⁻¹) Finset.univ (fun pq => pc v w ub pq.1 pq.2 ᵥ* pm (x i j hij t)⁻¹)
    hv' h2']
  refine conj_prod hX _ Finset.univ _ _ fun pq => ?_
  rw [coe_txc, coe_txc, tx_conj_x hX h5 hij t (smul_dot (ua ⬝ᵥ v) (pc_dot v w ub pq.1 pq.2))
    (p := pq.1) (q := pq.2)
    (fun l h1 h2 => by rw [Pi.smul_apply, pc_apply_of_ne v w ub h1 h2, smul_zero]),
    smul_vecMul, dot_transform]

#audit_axioms Xa_conj_x

/-- **Tulenbaev's Lemma 1.3(b)**: `α X_{v,bw}(a) α⁻¹ = X_{αv, bwα⁻¹}(a)` for all `α ∈ St(A)`,
with `a = u_a v` and `b = u_b v`. -/
theorem Xa_conj (h5 : 5 ≤ Fintype.card I) (α : SteinbergGroup I A) :
    ∀ (v w ua ub : I → A), w ⬝ᵥ v = 0 →
      α * Xa hX (Nat.le_of_succ_le h5) v ((ub ⬝ᵥ v) • w) ua * α⁻¹ =
        Xa hX (Nat.le_of_succ_le h5) (pm α *ᵥ v) ((ub ⬝ᵥ v) • (w ᵥ* pm α⁻¹)) (ua ᵥ* pm α⁻¹) := by
  have hα : α ∈ Subgroup.closure
      (Set.range (PresentedGroup.of (rels := SteinbergGroup.relations (I := I) (R := A)))) := by
    rw [PresentedGroup.closure_range_of]
    exact Subgroup.mem_top α
  induction hα using Subgroup.closure_induction'' with
  | mem g hg =>
    obtain ⟨⟨i, j, hij, t⟩, rfl⟩ := hg
    intro v w ua ub hw
    exact Xa_conj_x hX h5 hij t ua ub hw
  | inv_mem g hg =>
    obtain ⟨⟨i, j, hij, t⟩, rfl⟩ := hg
    intro v w ua ub hw
    have e : (PresentedGroup.of ⟨i, j, hij, t⟩ : SteinbergGroup I A)⁻¹ = x i j hij (-t) :=
      (x_neg i j hij t).symm
    rw [e]
    exact Xa_conj_x hX h5 hij (-t) ua ub hw
  | one =>
    intro v w ua ub hw
    rw [one_mul, inv_one, mul_one, pm_one, one_mulVec, vecMul_one, vecMul_one]
  | mul g g' _ _ hg hg' =>
    intro v w ua ub hw
    have hw' : (w ᵥ* pm g'⁻¹) ⬝ᵥ (pm g' *ᵥ v) = 0 := by rw [dot_transform, hw]
    have h := hg (pm g' *ᵥ v) (w ᵥ* pm g'⁻¹) (ua ᵥ* pm g'⁻¹) (ub ᵥ* pm g'⁻¹) hw'
    rw [dot_transform] at h
    rw [show g * g' * Xa hX (Nat.le_of_succ_le h5) v ((ub ⬝ᵥ v) • w) ua * (g * g')⁻¹ =
        g * (g' * Xa hX (Nat.le_of_succ_le h5) v ((ub ⬝ᵥ v) • w) ua * g'⁻¹) * g⁻¹ by group,
      hg' v w ua ub hw, h, pm_mul, mul_inv_rev, pm_mul, ← mulVec_mulVec, vecMul_vecMul,
      vecMul_vecMul]

#audit_axioms Xa_conj

end TulElem
end K2Found
end BooneHigmanLinear
end GroupApproximation
