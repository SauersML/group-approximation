import GroupApproximation.CharClass.OddPProductEval
import GroupApproximation.CharClass.OddPShuffle
import GroupApproximation.CharClass.OddPTupleFunctor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Finsupp.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Placing two tuples side by side, on the full tuple model

One of the two chain maps the odd-primary Cartan comparison compares sends a generator to two
`p`-fold diagonals placed next to each other in `C(X)^{⊗2p}`.  This file is that placement on the
full model `tupAllMod K X m` of `OddPTupleD.lean`.  The target arity is `2 * m`, never `m + m`:
`OddPShuffle`'s `riffleEquiv` and `blockRotEquiv`, and the Cartan target functor, all live on
`Fin (2 * m)`, so stating the concatenation there means no cast between the two spellings appears.

## Main results

* `tupConcatSq` — the bilinear concatenation `tupAllMod K X m → tupAllMod K X m → tupAllMod K X (2 * m)`.
* `tupEvalAll_tupConcatSq` — the evaluation of a concatenation is the product of the evaluations.
* `tupDAll_tupConcatSq` — **the Leibniz formula**, with the sign `tupSignAll` on the left factor.
* `tupAllMap_tupConcatSq` — naturality in the space.
* `tupPermAll_blockPermSq_tupConcatSq` — a block-diagonal permutation acts blockwise, with no cross sign;
  `tupBlockRotAll_tupConcatSq` is the blockwise rotation.
* `tupEvalAll_tupPermAll` — the evaluation of a signed slot permutation, on homogeneous functionals.
* `mem_range_tupIncl_iff`, `tupRestrict`, `tupConcatSq_mem_range`, `tupDAll_mem_range`, … — the
  degree-`k` carrier inside the full model.

## Design

* **Two halves of `Fin (2 * m)`.**  `leftIdx m a = a` and `rightIdx m b = m + b`, packaged as the
  equivalence `sqSumEquiv m : Fin m ⊕ Fin m ≃ Fin (2 * m)`; every sum, product and function on
  `Fin (2 * m)` is split through it, so no `Fin` arithmetic survives past the order lemmas.
* **Basis first, bilinearity second.**  Every identity is proved on basis tuples and extended by
  `Finsupp.induction_linear` in each argument.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. The two halves of `Fin (2 * m)` -/

section Halves

variable {m : ℕ}

/-- Slot `a` of the left block of `Fin (2 * m)`. -/
def leftIdx (m : ℕ) (a : Fin m) : Fin (2 * m) := ⟨a, by have := a.2; omega⟩

/-- Slot `b` of the right block of `Fin (2 * m)`. -/
def rightIdx (m : ℕ) (b : Fin m) : Fin (2 * m) := ⟨m + b, by have := b.2; omega⟩

theorem leftIdx_val (a : Fin m) : ((leftIdx m a : Fin (2 * m)) : ℕ) = a := rfl

theorem rightIdx_val (b : Fin m) : ((rightIdx m b : Fin (2 * m)) : ℕ) = m + b := rfl

theorem leftIdx_lt_leftIdx_iff (a b : Fin m) : leftIdx m a < leftIdx m b ↔ a < b := by
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, leftIdx_val, leftIdx_val]

theorem rightIdx_lt_rightIdx_iff (a b : Fin m) : rightIdx m a < rightIdx m b ↔ a < b := by
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, rightIdx_val, rightIdx_val]
  omega

theorem leftIdx_lt_rightIdx_iff (a b : Fin m) : leftIdx m a < rightIdx m b ↔ True := by
  rw [Fin.lt_iff_val_lt_val, leftIdx_val, rightIdx_val, iff_true]
  have := a.2
  omega

theorem rightIdx_lt_leftIdx_iff (a b : Fin m) : rightIdx m a < leftIdx m b ↔ False := by
  rw [Fin.lt_iff_val_lt_val, leftIdx_val, rightIdx_val, iff_false]
  have := b.2
  omega

theorem leftIdx_injective : Function.Injective (leftIdx m) := fun a b h => by
  have h' : (a : ℕ) = (b : ℕ) := congrArg Fin.val h
  exact Fin.ext h'

theorem rightIdx_injective : Function.Injective (rightIdx m) := fun a b h => by
  have h' : m + (a : ℕ) = m + (b : ℕ) := congrArg Fin.val h
  exact Fin.ext (by omega)

theorem leftIdx_ne_rightIdx (a b : Fin m) : leftIdx m a ≠ rightIdx m b := fun h => by
  have h' : (a : ℕ) = m + (b : ℕ) := congrArg Fin.val h
  have := a.2
  omega

/-- **`Fin (2 * m)` is two copies of `Fin m`**: the left block, then the right block. -/
def sqSumEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) where
  toFun := Sum.elim (leftIdx m) (rightIdx m)
  invFun i :=
    if h : (i : ℕ) < m then Sum.inl ⟨i, h⟩ else Sum.inr ⟨(i : ℕ) - m, by have := i.2; omega⟩
  left_inv x := by
    rcases x with a | b
    · show (if h : (a : ℕ) < m then Sum.inl ⟨a, h⟩ else Sum.inr ⟨(a : ℕ) - m, _⟩) = Sum.inl a
      rw [dif_pos a.2]
    · show (if h : m + (b : ℕ) < m then Sum.inl ⟨m + (b : ℕ), h⟩
          else Sum.inr ⟨m + (b : ℕ) - m, _⟩) = Sum.inr b
      rw [dif_neg (show ¬ (m + (b : ℕ) < m) by omega)]
      exact congrArg Sum.inr (Fin.ext (show m + (b : ℕ) - m = b by omega))
  right_inv i := by
    have hi := i.2
    by_cases h : (i : ℕ) < m
    · show Sum.elim (leftIdx m) (rightIdx m)
          (if h : (i : ℕ) < m then Sum.inl ⟨i, h⟩ else Sum.inr ⟨(i : ℕ) - m, _⟩) = i
      rw [dif_pos h]
      exact Fin.ext rfl
    · show Sum.elim (leftIdx m) (rightIdx m)
          (if h : (i : ℕ) < m then Sum.inl ⟨i, h⟩ else Sum.inr ⟨(i : ℕ) - m, _⟩) = i
      rw [dif_neg h]
      exact Fin.ext (show m + ((i : ℕ) - m) = i by omega)

theorem sqSumEquiv_inl (a : Fin m) : sqSumEquiv m (Sum.inl a) = leftIdx m a := rfl

theorem sqSumEquiv_inr (b : Fin m) : sqSumEquiv m (Sum.inr b) = rightIdx m b := rfl

theorem sqSumEquiv_symm_leftIdx (a : Fin m) : (sqSumEquiv m).symm (leftIdx m a) = Sum.inl a :=
  (Equiv.symm_apply_eq _).mpr rfl

theorem sqSumEquiv_symm_rightIdx (b : Fin m) : (sqSumEquiv m).symm (rightIdx m b) = Sum.inr b :=
  (Equiv.symm_apply_eq _).mpr rfl

/-- **A sum over `Fin (2 * m)`** is the sum over the left block plus the sum over the right block. -/
theorem sum_fin_two_mul {M : Type*} [AddCommMonoid M] (f : Fin (2 * m) → M) :
    ∑ i, f i = ∑ a, f (leftIdx m a) + ∑ b, f (rightIdx m b) := by
  rw [← Equiv.sum_comp (sqSumEquiv m) f, Fintype.sum_sum_type]
  rfl

/-- **A product over `Fin (2 * m)`** is the product over the left block times the product over the
right block. -/
theorem prod_fin_two_mul {M : Type*} [CommMonoid M] (f : Fin (2 * m) → M) :
    ∏ i, f i = (∏ a, f (leftIdx m a)) * ∏ b, f (rightIdx m b) := by
  rw [← Equiv.prod_comp (sqSumEquiv m) f, Fintype.prod_sum_type]
  rfl

/-- Two functions on `Fin (2 * m)` that agree on both blocks are equal. -/
theorem fin_two_mul_funext {α : Sort*} {f g : Fin (2 * m) → α}
    (hl : ∀ a, f (leftIdx m a) = g (leftIdx m a))
    (hr : ∀ b, f (rightIdx m b) = g (rightIdx m b)) : f = g := by
  funext i
  obtain ⟨x, rfl⟩ := (sqSumEquiv m).surjective i
  rcases x with a | b
  · exact hl a
  · exact hr b

/-- **The block-diagonal permutation** `π ⊔ ρ` of `Fin (2 * m)`: `π` on the left block, `ρ` on the
right block. -/
def blockPermSq (π ρ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (2 * m)) :=
  (sqSumEquiv m).permCongr (Equiv.Perm.sumCongr π ρ)

theorem blockPermSq_leftIdx (π ρ : Equiv.Perm (Fin m)) (a : Fin m) :
    blockPermSq π ρ (leftIdx m a) = leftIdx m (π a) := by
  rw [blockPermSq, Equiv.permCongr_apply, sqSumEquiv_symm_leftIdx, Equiv.Perm.sumCongr_apply,
    Sum.map_inl, sqSumEquiv_inl]

theorem blockPermSq_rightIdx (π ρ : Equiv.Perm (Fin m)) (b : Fin m) :
    blockPermSq π ρ (rightIdx m b) = rightIdx m (ρ b) := by
  rw [blockPermSq, Equiv.permCongr_apply, sqSumEquiv_symm_rightIdx, Equiv.Perm.sumCongr_apply,
    Sum.map_inr, sqSumEquiv_inr]

/-- **The blockwise rotation of `OddPShuffle` is the block-diagonal permutation of two rotations.** -/
theorem blockRotEquiv_eq_blockPermSq (m : ℕ) :
    blockRotEquiv m = blockPermSq (finRotate m) (finRotate m) := by
  refine Equiv.ext fun i => ?_
  obtain ⟨x, rfl⟩ := (sqSumEquiv m).surjective i
  rcases x with a | b
  · show blockRotEquiv m (leftIdx m a) = blockPermSq (finRotate m) (finRotate m) (leftIdx m a)
    rw [blockPermSq_leftIdx]
    apply Fin.ext
    rw [blockRotEquiv_val, leftIdx_val, leftIdx_val, finRotate_val_eq_ite]
    have := a.2
    unfold blockRotSrc
    split_ifs <;> omega
  · show blockRotEquiv m (rightIdx m b) = blockPermSq (finRotate m) (finRotate m) (rightIdx m b)
    rw [blockPermSq_rightIdx]
    apply Fin.ext
    rw [blockRotEquiv_val, rightIdx_val, rightIdx_val, finRotate_val_eq_ite]
    have := b.2
    unfold blockRotSrc
    split_ifs <;> omega

end Halves

/-! ## 2. Concatenated tuples -/

section Tuples

variable {m : ℕ}

/-- **Concatenate two `m`-tuples** into a `2m`-tuple: the left block from `u`, the right block from
`v`. -/
def tupAppendSq {α : Type*} (m : ℕ) (u v : Fin m → α) : Fin (2 * m) → α :=
  fun i => if h : (i : ℕ) < m then u ⟨i, h⟩ else v ⟨(i : ℕ) - m, by have := i.2; omega⟩

theorem tupAppendSq_leftIdx {α : Type*} (u v : Fin m → α) (a : Fin m) :
    tupAppendSq m u v (leftIdx m a) = u a := by
  show (if h : (a : ℕ) < m then u ⟨a, h⟩ else v ⟨(a : ℕ) - m, _⟩) = u a
  rw [dif_pos a.2]

theorem tupAppendSq_rightIdx {α : Type*} (u v : Fin m → α) (b : Fin m) :
    tupAppendSq m u v (rightIdx m b) = v b := by
  show (if h : m + (b : ℕ) < m then u ⟨m + (b : ℕ), h⟩ else v ⟨m + (b : ℕ) - m, _⟩) = v b
  rw [dif_neg (show ¬ (m + (b : ℕ) < m) by omega)]
  exact congrArg v (Fin.ext (show m + (b : ℕ) - m = b by omega))

theorem tupAppendSq_update_left {α : Type*} (u v : Fin m → α) (a : Fin m) (x : α) :
    Function.update (tupAppendSq m u v) (leftIdx m a) x
      = tupAppendSq m (Function.update u a x) v := by
  refine fin_two_mul_funext (fun a' => ?_) (fun b => ?_)
  · rw [tupAppendSq_leftIdx]
    by_cases h : a' = a
    · subst h
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun he => h (leftIdx_injective he)), Function.update_of_ne h,
        tupAppendSq_leftIdx]
  · rw [Function.update_of_ne (leftIdx_ne_rightIdx a b).symm, tupAppendSq_rightIdx,
      tupAppendSq_rightIdx]

theorem tupAppendSq_update_right {α : Type*} (u v : Fin m → α) (b : Fin m) (x : α) :
    Function.update (tupAppendSq m u v) (rightIdx m b) x
      = tupAppendSq m u (Function.update v b x) := by
  refine fin_two_mul_funext (fun a => ?_) (fun b' => ?_)
  · rw [Function.update_of_ne (leftIdx_ne_rightIdx a b), tupAppendSq_leftIdx,
      tupAppendSq_leftIdx]
  · rw [tupAppendSq_rightIdx]
    by_cases h : b' = b
    · subst h
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun he => h (rightIdx_injective he)), Function.update_of_ne h,
        tupAppendSq_rightIdx]

variable {X : TopCat.{0}}

/-- The prefix of a left-block slot of a concatenation is the prefix in the left tuple. -/
theorem tupPre_tupAppendSq_leftIdx (t u : TupAll X m) (a : Fin m) :
    tupPre (tupAppendSq m t u) (leftIdx m a) = tupPre t a := by
  rw [tupPre_eq_sum_ite, tupPre_eq_sum_ite, sum_fin_two_mul]
  simp only [leftIdx_lt_leftIdx_iff, rightIdx_lt_leftIdx_iff, ↓reduceIte, Finset.sum_const_zero,
    add_zero, tupAppendSq_leftIdx]

/-- The prefix of a right-block slot of a concatenation is the whole left total plus the prefix in
the right tuple. -/
theorem tupPre_tupAppendSq_rightIdx (t u : TupAll X m) (b : Fin m) :
    tupPre (tupAppendSq m t u) (rightIdx m b) = (∑ j, (t j).1) + tupPre u b := by
  rw [tupPre_eq_sum_ite, tupPre_eq_sum_ite, sum_fin_two_mul]
  simp only [leftIdx_lt_rightIdx_iff, rightIdx_lt_rightIdx_iff, ↓reduceIte, tupAppendSq_leftIdx,
    tupAppendSq_rightIdx]

/-- The total degree of a concatenation is the sum of the two totals. -/
theorem tupTot_tupAppendSq (t u : TupAll X m) :
    ∑ i, (tupAppendSq m t u i).1 = ∑ j, (t j).1 + ∑ j, (u j).1 := by
  rw [sum_fin_two_mul]
  simp only [tupAppendSq_leftIdx, tupAppendSq_rightIdx]

/-- Pushing a concatenation forward is concatenating the pushforwards. -/
theorem tupPush_tupAppendSq {Y : TopCat.{0}} (f : X ⟶ Y) (t u : TupAll X m) :
    tupPush f (tupAppendSq m t u) = tupAppendSq m (tupPush f t) (tupPush f u) :=
  fin_two_mul_funext
    (fun a => (congrArg (tagPush f) (tupAppendSq_leftIdx t u a)).trans
      (tupAppendSq_leftIdx (tupPush f t) (tupPush f u) a).symm)
    (fun b => (congrArg (tagPush f) (tupAppendSq_rightIdx t u b)).trans
      (tupAppendSq_rightIdx (tupPush f t) (tupPush f u) b).symm)

/-- A block-diagonal permutation of a concatenation permutes each block. -/
theorem permTup_blockPermSq (π ρ : Equiv.Perm (Fin m)) (t u : TupAll X m) :
    permTup (blockPermSq π ρ) (tupAppendSq m t u) = tupAppendSq m (permTup π t) (permTup ρ u) :=
  fin_two_mul_funext
    (fun a => (congrArg (tupAppendSq m t u) (blockPermSq_leftIdx π ρ a)).trans
      ((tupAppendSq_leftIdx t u (π a)).trans
        (tupAppendSq_leftIdx (permTup π t) (permTup ρ u) a).symm))
    (fun b => (congrArg (tupAppendSq m t u) (blockPermSq_rightIdx π ρ b)).trans
      ((tupAppendSq_rightIdx t u (ρ b)).trans
        (tupAppendSq_rightIdx (permTup π t) (permTup ρ u) b).symm))

/-- **No cross sign**: the Koszul exponent of a block-diagonal permutation of a concatenation is the
sum of the two exponents, because no pair of slots from different blocks is reordered. -/
theorem permExp_blockPermSq (π ρ : Equiv.Perm (Fin m)) (t u : TupAll X m) :
    permExp X (blockPermSq π ρ) (tupAppendSq m t u) = permExp X π t + permExp X ρ u := by
  unfold permExp
  rw [sum_fin_two_mul]
  simp only [sum_fin_two_mul, blockPermSq_leftIdx, blockPermSq_rightIdx, tupAppendSq_leftIdx,
    tupAppendSq_rightIdx, leftIdx_lt_leftIdx_iff, rightIdx_lt_rightIdx_iff, leftIdx_lt_rightIdx_iff,
    rightIdx_lt_leftIdx_iff, and_false, false_and, true_and, and_true, ↓reduceIte,
    Finset.sum_const_zero, add_zero, zero_add]

end Tuples

/-! ## 3. The concatenation and the sign involution on the full model -/

/-- **The bilinear concatenation** of the full model: on basis tuples, `single t ⊗ single u ↦
single (tupAppendSq m t u)`. -/
def tupConcatSq (K : Type) [CommRing K] (X : TopCat.{0}) (m : ℕ) :
    tupAllMod K X m →ₗ[K] tupAllMod K X m →ₗ[K] tupAllMod K X (2 * m) :=
  Finsupp.linearCombination K
    (fun t : TupAll X m => Finsupp.lmapDomain K K (fun u : TupAll X m => tupAppendSq m t u))

/-- **The grading involution** of the full model: a tuple of total degree `N` is multiplied by
`(-1)^N`. -/
def tupSignAll (K : Type) [CommRing K] (X : TopCat.{0}) (r : ℕ) : Module.End K (tupAllMod K X r) :=
  Finsupp.linearCombination K
    (fun t : TupAll X r => ((-1 : K) ^ (∑ j, (t j).1)) • Finsupp.single t (1 : K))

section FullModel

variable (K : Type) [CommRing K] {X : TopCat.{0}} {m r : ℕ}

theorem tupConcatSq_single_left (t : TupAll X m) (y : tupAllMod K X m) :
    tupConcatSq K X m (Finsupp.single t (1 : K)) y
      = Finsupp.lmapDomain K K (fun u : TupAll X m => tupAppendSq m t u) y := by
  rw [tupConcatSq, Finsupp.linearCombination_single, one_smul]

theorem tupConcatSq_single_single (t u : TupAll X m) :
    tupConcatSq K X m (Finsupp.single t (1 : K)) (Finsupp.single u (1 : K))
      = Finsupp.single (tupAppendSq m t u) (1 : K) := by
  rw [tupConcatSq_single_left, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem tupConcatSq_apply_single_right (x : tupAllMod K X m) (u : TupAll X m) :
    tupConcatSq K X m x (Finsupp.single u (1 : K))
      = Finsupp.lmapDomain K K (fun t : TupAll X m => tupAppendSq m t u) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, map_add]
  | single t a =>
    have hs : Finsupp.single t a = a • Finsupp.single t (1 : K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, LinearMap.smul_apply, tupConcatSq_single_single, map_smul,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem tupSignAll_single (t : TupAll X r) :
    tupSignAll K X r (Finsupp.single t (1 : K))
      = ((-1 : K) ^ (∑ j, (t j).1)) • Finsupp.single t (1 : K) := by
  rw [tupSignAll, Finsupp.linearCombination_single, one_smul]

/-- On the degree-`k` carrier the grading involution is the constant sign `(-1)^k`. -/
theorem tupSignAll_tupIncl (k : ℕ) (x : tupMod K X r k) :
    tupSignAll K X r (tupIncl K X r k x) = (-1 : K) ^ k • tupIncl K X r k x := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | single t a =>
    have hs : Finsupp.single t a = a • Finsupp.single t (1 : K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul, tupIncl_single, tupSignAll_single, t.2, smul_comm]

/-! ## 4. Evaluation -/

/-- The evaluation of a concatenated basis tuple is the product of the two evaluations. -/
theorem tupEvalAll_tupConcatSq_single (φ ψ : Fin m → ∀ n : ℕ, singularCochainGroup K X n)
    (t u : TupAll X m) :
    tupEvalAll K X (2 * m) (tupAppendSq m φ ψ) (Finsupp.single (tupAppendSq m t u) (1 : K))
      = tupEvalAll K X m φ (Finsupp.single t (1 : K))
          * tupEvalAll K X m ψ (Finsupp.single u (1 : K)) := by
  rw [tupEvalAll_single, tupEvalAll_single, tupEvalAll_single, prod_fin_two_mul]
  simp only [tupAppendSq_leftIdx, tupAppendSq_rightIdx]

/-- **The evaluation of a concatenation is the product of the evaluations**, against the
concatenated graded cochains. -/
theorem tupEvalAll_tupConcatSq (φ ψ : Fin m → ∀ n : ℕ, singularCochainGroup K X n)
    (x y : tupAllMod K X m) :
    tupEvalAll K X (2 * m) (tupAppendSq m φ ψ) (tupConcatSq K X m x y)
      = tupEvalAll K X m φ x * tupEvalAll K X m ψ y := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply, zero_mul]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂, add_mul]
  | single t a =>
    induction y using Finsupp.induction_linear with
    | zero => simp only [map_zero, mul_zero]
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂, mul_add]
    | single u c =>
      have ht : Finsupp.single t a = a • Finsupp.single t (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hu : Finsupp.single u c = c • Finsupp.single u (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [ht, hu, map_smul, LinearMap.smul_apply, map_smul, tupConcatSq_single_single, map_smul,
        map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        tupEvalAll_tupConcatSq_single]
      ring

/-- The concatenated graded cochains are homogeneous in the concatenated degrees. -/
theorem isHomogFun_tupAppendSq {φ ψ : Fin m → ∀ n : ℕ, singularCochainGroup K X n}
    {d e : Fin m → ℕ} (hφ : IsHomogFun K φ d) (hψ : IsHomogFun K ψ e) :
    IsHomogFun K (tupAppendSq m φ ψ) (tupAppendSq m d e) := by
  intro i n hn
  obtain ⟨x, rfl⟩ := (sqSumEquiv m).surjective i
  rcases x with a | b
  · rw [sqSumEquiv_inl] at hn ⊢
    rw [tupAppendSq_leftIdx] at hn ⊢
    exact hφ a n hn
  · rw [sqSumEquiv_inr] at hn ⊢
    rw [tupAppendSq_rightIdx] at hn ⊢
    exact hψ b n hn

/-- The evaluation of a signed slot permutation of one basis tuple, on a homogeneous functional. -/
theorem tupEvalAll_tupPermAll_single (π : Equiv.Perm (Fin r))
    (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (d : Fin r → ℕ) (hφ : IsHomogFun K φ d)
    (t : TupAll X r) :
    tupEvalAll K X r φ (tupPermAll K X r π (Finsupp.single t (1 : K)))
      = (-1 : K) ^ (∑ i : Fin r, ∑ j : Fin r, if i < j ∧ π j < π i then d i * d j else 0)
          * tupEvalAll K X r (φ ∘ ⇑π.symm) (Finsupp.single t (1 : K)) := by
  rw [tupPermAll_single, map_smul, smul_eq_mul, tupEvalAll_single, tupEvalAll_single]
  have hre : ∏ j, tagEvalG K ((φ ∘ ⇑π.symm) j) (t j)
      = ∏ j, tagEvalG K (φ j) (permTup π t j) := by
    rw [← Equiv.prod_comp π (fun i => tagEvalG K ((φ ∘ ⇑π.symm) i) (t i))]
    refine Finset.prod_congr rfl fun j _ => ?_
    show tagEvalG K (φ (π.symm (π j))) (t (π j)) = tagEvalG K (φ j) (t (π j))
    rw [Equiv.symm_apply_apply]
  rw [hre]
  by_cases hall : ∀ j, (permTup π t j).1 = d j
  · have hE : permExp X π t
        = ∑ i : Fin r, ∑ j : Fin r, if i < j ∧ π j < π i then d i * d j else 0 := by
      unfold permExp
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hi : (t (π i)).1 = d i := hall i
      have hj : (t (π j)).1 = d j := hall j
      rw [hi, hj]
    rw [hE]
  · obtain ⟨j, hj⟩ := not_forall.mp hall
    have h0 : ∏ l, tagEvalG K (φ l) (permTup π t l) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (tagEvalG_of_eq_zero K (φ j) _ (hφ j _ hj))
    rw [h0, mul_zero, mul_zero]

/-- **The evaluation of a signed slot permutation**, on a homogeneous functional: the Koszul sign of
the prescribed degrees times the evaluation against the permuted cochains. -/
theorem tupEvalAll_tupPermAll (π : Equiv.Perm (Fin r))
    (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (d : Fin r → ℕ) (hφ : IsHomogFun K φ d)
    (x : tupAllMod K X r) :
    tupEvalAll K X r φ (tupPermAll K X r π x)
      = (-1 : K) ^ (∑ i : Fin r, ∑ j : Fin r, if i < j ∧ π j < π i then d i * d j else 0)
          * tupEvalAll K X r (φ ∘ ⇑π.symm) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, mul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | single t a =>
    have hs : Finsupp.single t a = a • Finsupp.single t (1 : K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      tupEvalAll_tupPermAll_single K π φ d hφ t]
    ring

/-! ## 5. The Leibniz formula -/

/-- **The Leibniz formula on basis tuples.** -/
theorem tupDAll_tupConcatSq_single (t u : TupAll X m) :
    tupDAll K X (2 * m) (Finsupp.single (tupAppendSq m t u) (1 : K))
      = tupConcatSq K X m (tupDAll K X m (Finsupp.single t (1 : K))) (Finsupp.single u (1 : K))
        + tupConcatSq K X m (tupSignAll K X m (Finsupp.single t (1 : K)))
            (tupDAll K X m (Finsupp.single u (1 : K))) := by
  rw [tupDAll, LinearMap.sum_apply, sum_fin_two_mul]
  congr 1
  · rw [tupDAll, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotBd_single, slotBd_single, slotBdGen, slotBdGen, tupConcatSq_apply_single_right,
      map_smul, Finsupp.apply_linearCombination, tupPre_tupAppendSq_leftIdx, tupAppendSq_leftIdx]
    congr 1
    refine tupLC_congr_fun K (fun τ => ?_) _
    show Finsupp.single (Function.update (tupAppendSq m t u) (leftIdx m a) τ) (1 : K)
      = Finsupp.lmapDomain K K (fun t' : TupAll X m => tupAppendSq m t' u)
          (Finsupp.single (Function.update t a τ) (1 : K))
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, tupAppendSq_update_left]
  · rw [tupSignAll_single, map_smul, LinearMap.smul_apply, tupConcatSq_single_left, tupDAll,
      LinearMap.sum_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [slotBd_single, slotBd_single, slotBdGen, slotBdGen, map_smul, smul_smul,
      Finsupp.apply_linearCombination, tupPre_tupAppendSq_rightIdx, tupAppendSq_rightIdx, pow_add]
    congr 1
    refine tupLC_congr_fun K (fun τ => ?_) _
    show Finsupp.single (Function.update (tupAppendSq m t u) (rightIdx m b) τ) (1 : K)
      = Finsupp.lmapDomain K K (fun u' : TupAll X m => tupAppendSq m t u')
          (Finsupp.single (Function.update u b τ) (1 : K))
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, tupAppendSq_update_right]

/-- **The Leibniz formula**: `d (x ⊗ y) = d x ⊗ y + ε(x) ⊗ d y`, with the grading involution `ε` on
the left factor. -/
theorem tupDAll_tupConcatSq (x y : tupAllMod K X m) :
    tupDAll K X (2 * m) (tupConcatSq K X m x y)
      = tupConcatSq K X m (tupDAll K X m x) y
        + tupConcatSq K X m (tupSignAll K X m x) (tupDAll K X m y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply, add_zero]
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, h₁, h₂]
    abel
  | single t a =>
    induction y using Finsupp.induction_linear with
    | zero => simp only [map_zero, add_zero]
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, h₁, h₂]
      abel
    | single u c =>
      have ht : Finsupp.single t a = a • Finsupp.single t (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hu : Finsupp.single u c = c • Finsupp.single u (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [ht, hu]
      simp only [map_smul, LinearMap.smul_apply, tupConcatSq_single_single]
      rw [tupDAll_tupConcatSq_single, smul_add, smul_add]

/-! ## 6. Naturality and block-diagonal permutations -/

/-- **The concatenation is natural in the space.** -/
theorem tupAllMap_tupConcatSq {Y : TopCat.{0}} (f : X ⟶ Y) (x y : tupAllMod K X m) :
    tupAllMap K f (2 * m) (tupConcatSq K X m x y)
      = tupConcatSq K Y m (tupAllMap K f m x) (tupAllMap K f m y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | single t a =>
    induction y using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | single u c =>
      have ht : Finsupp.single t a = a • Finsupp.single t (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hu : Finsupp.single u c = c • Finsupp.single u (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [ht, hu]
      simp only [map_smul, LinearMap.smul_apply, tupConcatSq_single_single, tupAllMap_single,
        tupPush_tupAppendSq]

/-- A block-diagonal permutation of one concatenated basis tuple. -/
theorem tupPermAll_blockPermSq_single (π ρ : Equiv.Perm (Fin m)) (t u : TupAll X m) :
    tupPermAll K X (2 * m) (blockPermSq π ρ) (Finsupp.single (tupAppendSq m t u) (1 : K))
      = tupConcatSq K X m (tupPermAll K X m π (Finsupp.single t (1 : K)))
          (tupPermAll K X m ρ (Finsupp.single u (1 : K))) := by
  rw [tupPermAll_single, tupPermAll_single, tupPermAll_single, map_smul, LinearMap.smul_apply,
    map_smul, tupConcatSq_single_single, smul_smul, permExp_blockPermSq, pow_add,
    permTup_blockPermSq]

/-- **A block-diagonal permutation acts blockwise**, with no cross sign. -/
theorem tupPermAll_blockPermSq_tupConcatSq (π ρ : Equiv.Perm (Fin m)) (x y : tupAllMod K X m) :
    tupPermAll K X (2 * m) (blockPermSq π ρ) (tupConcatSq K X m x y)
      = tupConcatSq K X m (tupPermAll K X m π x) (tupPermAll K X m ρ y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | single t a =>
    induction y using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | single u c =>
      have ht : Finsupp.single t a = a • Finsupp.single t (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hu : Finsupp.single u c = c • Finsupp.single u (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [ht, hu]
      simp only [map_smul, LinearMap.smul_apply, tupConcatSq_single_single]
      rw [tupPermAll_blockPermSq_single]

/-- **The blockwise rotation of a concatenation is the concatenation of the two rotations.** -/
theorem tupBlockRotAll_tupConcatSq (x y : tupAllMod K X m) :
    tupBlockRotAll K X m (tupConcatSq K X m x y)
      = tupConcatSq K X m (tupTAll K X m x) (tupTAll K X m y) := by
  rw [tupBlockRotAll, blockRotEquiv_eq_blockPermSq, tupPermAll_blockPermSq_tupConcatSq,
    tupTAll_eq_tupPermAll]

/-! ## 7. The degree-`k` carrier inside the full model -/

/-- The degree-`k` coefficients of an element of the full model. -/
def tupRestrict (K : Type) [CommRing K] (X : TopCat.{0}) (r k : ℕ) :
    tupAllMod K X r →ₗ[K] tupMod K X r k :=
  Finsupp.lcomapDomain Subtype.val Subtype.val_injective

theorem tupRestrict_tupIncl (k : ℕ) (x : tupMod K X r k) :
    tupRestrict K X r k (tupIncl K X r k x) = x :=
  Finsupp.comapDomain_mapDomain Subtype.val_injective x

/-- An element of the full model concentrated in total degree `k`. -/
def IsTupDeg (k : ℕ) (z : tupAllMod K X r) : Prop := ∀ t, z t ≠ 0 → ∑ j, (t j).1 = k

/-- **The degree-`k` carrier is the set of elements concentrated in total degree `k`.** -/
theorem mem_range_tupIncl_iff {k : ℕ} {z : tupAllMod K X r} :
    z ∈ LinearMap.range (tupIncl K X r k) ↔ IsTupDeg K k z := by
  constructor
  · intro hz t ht
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
    by_contra hne
    apply ht
    show Finsupp.mapDomain Subtype.val x t = 0
    refine Finsupp.mapDomain_notin_range x t ?_
    rintro ⟨s, hs⟩
    exact hne (hs ▸ s.2)
  · intro hz
    refine LinearMap.mem_range.mpr ⟨tupRestrict K X r k z, ?_⟩
    show Finsupp.mapDomain Subtype.val
        (Finsupp.comapDomain Subtype.val z Subtype.val_injective.injOn) = z
    refine Finsupp.mapDomain_comapDomain Subtype.val_injective z ?_
    intro t ht
    exact ⟨⟨t, hz t (Finsupp.mem_support_iff.mp ht)⟩, rfl⟩

theorem tupIncl_tupRestrict {k : ℕ} {z : tupAllMod K X r}
    (hz : z ∈ LinearMap.range (tupIncl K X r k)) :
    tupIncl K X r k (tupRestrict K X r k z) = z := by
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
  rw [tupRestrict_tupIncl]

/-- Concatenating degrees `k` and `k'` gives degree `k + k'`. -/
theorem tupConcatSq_mem_range {k k' : ℕ} {x y : tupAllMod K X m}
    (hx : x ∈ LinearMap.range (tupIncl K X m k)) (hy : y ∈ LinearMap.range (tupIncl K X m k')) :
    tupConcatSq K X m x y ∈ LinearMap.range (tupIncl K X (2 * m) (k + k')) := by
  obtain ⟨x', rfl⟩ := LinearMap.mem_range.mp hx
  obtain ⟨y', rfl⟩ := LinearMap.mem_range.mp hy
  induction x' using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ ha hb
  | single t c =>
    induction y' using Finsupp.induction_linear with
    | zero =>
      rw [map_zero, map_zero]
      exact Submodule.zero_mem _
    | add a b ha hb =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
    | single u c' =>
      have ht : Finsupp.single t c = c • Finsupp.single t (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hu : Finsupp.single u c' = c' • Finsupp.single u (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [ht, hu, map_smul, map_smul, map_smul, LinearMap.smul_apply, map_smul, tupIncl_single,
        tupIncl_single, tupConcatSq_single_single]
      refine Submodule.smul_mem _ c (Submodule.smul_mem _ c' ?_)
      refine LinearMap.mem_range.mpr ⟨Finsupp.single ⟨tupAppendSq m t.1 u.1, ?_⟩ (1 : K), ?_⟩
      · rw [tupTot_tupAppendSq, t.2, u.2]
      · exact tupIncl_single K X (k + k') _

/-- The boundary lowers the degree by one. -/
theorem tupDAll_mem_range {k : ℕ} {z : tupAllMod K X r}
    (hz : z ∈ LinearMap.range (tupIncl K X r (k + 1))) :
    tupDAll K X r z ∈ LinearMap.range (tupIncl K X r k) := by
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
  exact LinearMap.mem_range.mpr ⟨tupD K X r k x, LinearMap.congr_fun (tupIncl_comp_tupD K X k) x⟩

/-- A signed slot permutation preserves the degree. -/
theorem tupPermAll_mem_range {k : ℕ} (π : Equiv.Perm (Fin r)) {z : tupAllMod K X r}
    (hz : z ∈ LinearMap.range (tupIncl K X r k)) :
    tupPermAll K X r π z ∈ LinearMap.range (tupIncl K X r k) := by
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
  exact LinearMap.mem_range.mpr
    ⟨tupPerm K X r k π x, LinearMap.congr_fun (tupIncl_comp_tupPerm K X k π) x⟩

/-- The grading involution preserves the degree. -/
theorem tupSignAll_mem_range {k : ℕ} {z : tupAllMod K X r}
    (hz : z ∈ LinearMap.range (tupIncl K X r k)) :
    tupSignAll K X r z ∈ LinearMap.range (tupIncl K X r k) := by
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
  rw [tupSignAll_tupIncl]
  exact Submodule.smul_mem _ _ (LinearMap.mem_range.mpr ⟨x, rfl⟩)

/-- The pushforward preserves the degree. -/
theorem tupAllMap_mem_range {Y : TopCat.{0}} {k : ℕ} (f : X ⟶ Y) {z : tupAllMod K X r}
    (hz : z ∈ LinearMap.range (tupIncl K X r k)) :
    tupAllMap K f r z ∈ LinearMap.range (tupIncl K Y r k) := by
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
  exact LinearMap.mem_range.mpr ⟨tupMap K f r k x, LinearMap.congr_fun (tupIncl_comp_tupMap K f k) x⟩

end FullModel

end

#audit_axioms tupEvalAll_tupConcatSq
#audit_axioms tupDAll_tupConcatSq
#audit_axioms tupAllMap_tupConcatSq
#audit_axioms tupPermAll_blockPermSq_tupConcatSq
#audit_axioms tupBlockRotAll_tupConcatSq
#audit_axioms tupEvalAll_tupPermAll
#audit_axioms tupConcatSq_mem_range

end GroupApproximation.CharClass
