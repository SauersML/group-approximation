import Mathlib.Data.Finset.NoncommProd
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Products over pairwise commuting root families (lane sk-leavitt-02, helpers)

For a finite index type `ι`, an additive monoid `A`, and a family `ϕ : ι → A → G` of maps into a
group, where any two values commute, `rootVecProd ϕ hcomm a = ∏ᵢ ϕ i (a i)` is a well-defined
`Finset.noncommProd`.  When every `ϕ i` is additive, this product is additive in `a`, it sends
`Function.update 0 i s` to `ϕ i s`, and it splits off any one coordinate.

The file also has a group identity for conjugating a split product, and the effect of the matrices
`1 + E_ij(c)` on column and row vectors.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
namespace RowColumn

open scoped Matrix

section Product

variable {ι A G : Type*} [Fintype ι] [DecidableEq ι] [AddMonoid A] [Group G]
  (ϕ : ι → A → G) (hcomm : ∀ (i j : ι) (s t : A), Commute (ϕ i s) (ϕ j t))

/-- `∏ᵢ ϕ i (a i)`, taken over a family whose values pairwise commute. -/
def rootVecProd (a : ι → A) : G :=
  Finset.univ.noncommProd (fun i => ϕ i (a i)) fun i _ j _ _ => hcomm i j (a i) (a j)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.rootVecProd

theorem rootVecProd_add (hadd : ∀ (i : ι) (s t : A), ϕ i (s + t) = ϕ i s * ϕ i t)
    (a b : ι → A) :
    rootVecProd ϕ hcomm (a + b) = rootVecProd ϕ hcomm a * rootVecProd ϕ hcomm b := by
  have h := Finset.noncommProd_mul_distrib (s := Finset.univ)
    (fun i => ϕ i (a i)) (fun i => ϕ i (b i))
    (fun i _ j _ _ => hcomm i j (a i) (a j)) (fun i _ j _ _ => hcomm i j (b i) (b j))
    (fun i _ j _ _ => hcomm i j (b i) (a j))
  refine Eq.trans ?_ h
  exact Finset.noncommProd_congr rfl
    (fun i _ => by simp only [Pi.add_apply, Pi.mul_apply, hadd]) _

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.rootVecProd_add

theorem rootVecProd_update_zero (hzero : ∀ i : ι, ϕ i 0 = 1) (i : ι) (s : A) :
    rootVecProd ϕ hcomm (Function.update (0 : ι → A) i s) = ϕ i s := by
  unfold rootVecProd
  have h1 : ∀ j ∈ Finset.univ.erase i, ϕ j (Function.update (0 : ι → A) i s j) = 1 := by
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), Pi.zero_apply, hzero]
  rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i) _ _,
    Finset.noncommProd_eq_pow_card _ _ _ (1 : G) h1, one_pow, mul_one]
  exact congrArg (ϕ i) (Function.update_self i s (0 : ι → A))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.rootVecProd_update_zero

theorem rootVecProd_commute (y : G) (a : ι → A) (h : ∀ i, Commute y (ϕ i (a i))) :
    Commute y (rootVecProd ϕ hcomm a) :=
  Finset.noncommProd_commute _ _ _ y fun i _ => h i

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.rootVecProd_commute

theorem rootVecProd_split (hadd : ∀ (i : ι) (s t : A), ϕ i (s + t) = ϕ i s * ϕ i t)
    (hzero : ∀ i : ι, ϕ i 0 = 1) (a : ι → A) (j : ι) :
    rootVecProd ϕ hcomm a = ϕ j (a j) * rootVecProd ϕ hcomm (Function.update a j 0) := by
  have hv : a = Function.update (0 : ι → A) j (a j) + Function.update a j 0 := by
    ext k
    by_cases hk : k = j
    · subst hk
      rw [Pi.add_apply, Function.update_self, Function.update_self, add_zero]
    · rw [Pi.add_apply, Function.update_of_ne hk, Function.update_of_ne hk, Pi.zero_apply,
        zero_add]
  calc rootVecProd ϕ hcomm a
      = rootVecProd ϕ hcomm (Function.update (0 : ι → A) j (a j) + Function.update a j 0) :=
        congrArg (rootVecProd ϕ hcomm) hv
    _ = ϕ j (a j) * rootVecProd ϕ hcomm (Function.update a j 0) := by
        rw [rootVecProd_add ϕ hcomm hadd, rootVecProd_update_zero ϕ hcomm hzero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.rootVecProd_split

end Product

/-- If `T = W * V`, conjugation by `z` sends `W` to `X * W`, and `z` commutes with `V`, then
conjugation by `z` sends `T` to `X * T`. -/
theorem conj_split {G : Type*} [Group G] (z W V X T : G) (hsplit : T = W * V)
    (hconj : z * W * z⁻¹ = X * W) (hcomm : Commute z V) : z * T * z⁻¹ = X * T := by
  rw [hsplit]
  calc z * (W * V) * z⁻¹ = (z * W * z⁻¹) * (z * V * z⁻¹) := by group
    _ = X * W * V := by rw [hconj, hcomm.eq, mul_inv_cancel_right]
    _ = X * (W * V) := mul_assoc _ _ _

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.conj_split

section Matrices

variable {n : ℕ} {R : Type*} [Ring R]

theorem one_add_single_mulVec (i j : Fin n) (c : R) (a : Fin n → R) :
    (1 + Matrix.single i j c) *ᵥ a = a + Function.update (0 : Fin n → R) i (c * a j) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.one_add_single_mulVec

theorem vecMul_single_eq (b : Fin n → R) (i j : Fin n) (c : R) :
    b ᵥ* Matrix.single i j c = Function.update (0 : Fin n → R) j (b i * c) := by
  ext k
  rw [Matrix.vecMul_apply_eq_sum, Finset.sum_eq_single i]
  · by_cases hk : k = j
    · subst hk
      rw [Matrix.single_apply_same, Function.update_self]
    · rw [Matrix.single_apply_of_col_ne i i (Ne.symm hk), mul_zero, Function.update_of_ne hk,
        Pi.zero_apply]
  · intro l _ hl
    rw [Matrix.single_apply_of_row_ne (Ne.symm hl), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.vecMul_single_eq

theorem vecMul_one_add_single (b : Fin n → R) (i j : Fin n) (c : R) :
    b ᵥ* (1 + Matrix.single i j c) = b + Function.update (0 : Fin n → R) j (b i * c) := by
  rw [Matrix.vecMul_add, Matrix.vecMul_one, vecMul_single_eq]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.vecMul_one_add_single

end Matrices

end RowColumn
end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
