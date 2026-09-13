import GroupApproximation.GraphCStar.KTheoryRelations
import GroupApproximation.KirchbergLoops.CokernelData
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring

/-!
# `coker(1 - Mᵀ)` and `ker(1 - Mᵀ)` for `E(u)`, `E(1,2)` and `E(1,1,2)`

The graph `E(u)` has vertex matrix `M(u) = 1 + u 1ᵀ` (`KirchbergLoops.graphMatrix`). This file
computes the two integer groups that graph-algebra K-theory identifies with `K₀` and `K₁`.

* `range_relationHom_graphMatrix`: the image of `1 - M(u)ᵀ` is `ℤu`, so the cokernel is `ℤⁿ/ℤu`.
* `mem_ker_relationHom_graphMatrix`: for `u ≠ 0`, the kernel is `{x | ∑ x = 0}`.
* `cokernelEquivB`, `cokernelEquivB_one`: `coker(1 - M(1,2)ᵀ) ≅ ℤ`, sending the class of `(1,1)`
  to `1`.
* `kernelEquivB`: `ker(1 - M(1,2)ᵀ) ≅ ℤ`.
* `cokernelEquivC`, `cokernelEquivC_one`: `coker(1 - M(1,1,2)ᵀ) ≅ ℤ²`, sending the class of
  `(1,1,1)` to `(1,0)`.
* `kernelEquivC`: `ker(1 - M(1,1,2)ᵀ) ≅ ℤ²`.

Only the integer side is proved here. `KTheoryRelations` maps these cokernels into `K₀` of any
`*`-ring carrying a Cuntz–Krieger family, and sends the class of `(1, …, 1)` to `[1]`. The file does
not prove `K₀(C*(E)) ≅ coker(1 - Mᵀ)` or `K₁(C*(E)) ≅ ker(1 - Mᵀ)`, and it says nothing about `B ⊗ B`.
-/

namespace GroupApproximation
namespace GraphCStar

open KirchbergLoops (graphMatrix one_sub_transpose_graphMatrix_mulVec)

section General

variable {n : ℕ}

/-- **The image of `1 - M(u)ᵀ` is `ℤu`.** -/
theorem range_relationHom_graphMatrix [NeZero n] (u : Fin n → ℤ) :
    (relationHom (graphMatrix u)).range = AddSubgroup.zmultiples u := by
  ext y
  rw [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨-∑ j, x j, (one_sub_transpose_graphMatrix_mulVec u x).symm⟩
  · rintro ⟨k, rfl⟩
    refine ⟨Pi.single 0 (-k), ?_⟩
    have h := one_sub_transpose_graphMatrix_mulVec u (Pi.single 0 (-k))
    simp only [Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte, neg_neg] at h
    exact h

/-- **The kernel of `1 - M(u)ᵀ` is `{x | ∑ x = 0}`** when `u ≠ 0`. -/
theorem mem_ker_relationHom_graphMatrix (u : Fin n → ℤ) (hu : u ≠ 0) (x : Fin n → ℤ) :
    x ∈ (relationHom (graphMatrix u)).ker ↔ ∑ j, x j = 0 := by
  rw [AddMonoidHom.mem_ker, relationHom_apply, one_sub_transpose_graphMatrix_mulVec]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
    have h' : -(∑ j, x j) * u i = 0 := congrFun h i
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact neg_eq_zero.1 h''
    · exact absurd h'' hi
  · intro h
    funext i
    show -(∑ j, x j) * u i = 0
    rw [h, neg_zero, zero_mul]

end General

section B

theorem ne_zero_B : (![1, 2] : Fin 2 → ℤ) ≠ 0 := fun h => by
  simpa using congrFun h 0

/-- `x ↦ 2x₀ - x₁`, whose kernel is `ℤ(1,2)`. -/
def formB : (Fin 2 → ℤ) →+ ℤ :=
  AddMonoidHom.mk' (fun x => 2 * x 0 - x 1) fun x y => by
    show 2 * (x 0 + y 0) - (x 1 + y 1) = (2 * x 0 - x 1) + (2 * y 0 - y 1)
    ring

theorem formB_apply (x : Fin 2 → ℤ) : formB x = 2 * x 0 - x 1 :=
  rfl

theorem ker_formB : formB.ker = (relationHom (graphMatrix ![1, 2])).range := by
  rw [range_relationHom_graphMatrix]
  ext x
  rw [AddMonoidHom.mem_ker, formB_apply, AddSubgroup.mem_zmultiples_iff]
  constructor
  · intro h
    refine ⟨x 0, funext fun i => ?_⟩
    fin_cases i
    · show x 0 * 1 = x 0
      omega
    · show x 0 * 2 = x 1
      omega
  · rintro ⟨k, rfl⟩
    show 2 * (k * 1) - k * 2 = 0
    ring

theorem surjective_formB : Function.Surjective formB := fun t =>
  ⟨![0, -t], by
    show 2 * 0 - -t = t
    ring⟩

/-- **`coker(1 - M(1,2)ᵀ) ≅ ℤ`**, induced by `x ↦ 2x₀ - x₁`. -/
noncomputable def cokernelEquivB : cokernel (graphMatrix ![1, 2]) ≃+ ℤ :=
  (QuotientAddGroup.quotientAddEquivOfEq ker_formB.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective formB surjective_formB)

theorem cokernelEquivB_mk (x : Fin 2 → ℤ) :
    cokernelEquivB (QuotientAddGroup.mk x) = 2 * x 0 - x 1 :=
  rfl

/-- **The class of `(1,1)` goes to `1`.** -/
theorem cokernelEquivB_one : cokernelEquivB (QuotientAddGroup.mk fun _ => 1) = 1 :=
  (cokernelEquivB_mk _).trans (by norm_num)

/-- **`ker(1 - M(1,2)ᵀ) ≅ ℤ`**, `x ↦ x₀`. -/
def kernelEquivB : (relationHom (graphMatrix ![1, 2])).ker ≃+ ℤ where
  toFun x := (x : Fin 2 → ℤ) 0
  invFun t := ⟨![t, -t], (mem_ker_relationHom_graphMatrix _ ne_zero_B _).2 (by
    rw [Fin.sum_univ_two]
    show t + -t = 0
    ring)⟩
  left_inv x := by
    have h := (mem_ker_relationHom_graphMatrix _ ne_zero_B _).1 x.2
    rw [Fin.sum_univ_two] at h
    refine Subtype.ext (funext fun i => ?_)
    fin_cases i
    · rfl
    · show -(x : Fin 2 → ℤ) 0 = (x : Fin 2 → ℤ) 1
      omega
  right_inv t := rfl
  map_add' x y := rfl

end B

section C

theorem ne_zero_C : (![1, 1, 2] : Fin 3 → ℤ) ≠ 0 := fun h => by
  simpa using congrFun h 0

/-- `x ↦ (2x₁ - x₂, x₀ - x₁)`, whose kernel is `ℤ(1,1,2)`. -/
def formC : (Fin 3 → ℤ) →+ (Fin 2 → ℤ) :=
  AddMonoidHom.mk' (fun x => ![2 * x 1 - x 2, x 0 - x 1]) fun x y => by
    funext i
    fin_cases i
    · show 2 * (x 1 + y 1) - (x 2 + y 2) = (2 * x 1 - x 2) + (2 * y 1 - y 2)
      ring
    · show x 0 + y 0 - (x 1 + y 1) = (x 0 - x 1) + (y 0 - y 1)
      ring

theorem formC_apply (x : Fin 3 → ℤ) : formC x = ![2 * x 1 - x 2, x 0 - x 1] :=
  rfl

theorem ker_formC : formC.ker = (relationHom (graphMatrix ![1, 1, 2])).range := by
  rw [range_relationHom_graphMatrix]
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_zmultiples_iff]
  constructor
  · intro h
    have h₀ : 2 * x 1 - x 2 = 0 := congrFun h 0
    have h₁ : x 0 - x 1 = 0 := congrFun h 1
    refine ⟨x 1, funext fun i => ?_⟩
    fin_cases i
    · show x 1 * 1 = x 0
      omega
    · show x 1 * 1 = x 1
      omega
    · show x 1 * 2 = x 2
      omega
  · rintro ⟨k, rfl⟩
    funext i
    fin_cases i
    · show 2 * (k * 1) - k * 2 = 0
      ring
    · show k * 1 - k * 1 = 0
      ring

theorem surjective_formC : Function.Surjective formC := fun y =>
  ⟨![y 1, 0, -y 0], funext fun i => by
    fin_cases i
    · show 2 * 0 - -y 0 = y 0
      ring
    · show y 1 - 0 = y 1
      ring⟩

/-- **`coker(1 - M(1,1,2)ᵀ) ≅ ℤ²`**, induced by `x ↦ (2x₁ - x₂, x₀ - x₁)`. -/
noncomputable def cokernelEquivC : cokernel (graphMatrix ![1, 1, 2]) ≃+ (Fin 2 → ℤ) :=
  (QuotientAddGroup.quotientAddEquivOfEq ker_formC.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective formC surjective_formC)

theorem cokernelEquivC_mk (x : Fin 3 → ℤ) :
    cokernelEquivC (QuotientAddGroup.mk x) = ![2 * x 1 - x 2, x 0 - x 1] :=
  rfl

/-- **The class of `(1,1,1)` goes to `(1,0)`.** -/
theorem cokernelEquivC_one :
    cokernelEquivC (QuotientAddGroup.mk fun _ => 1) = ![1, 0] :=
  (cokernelEquivC_mk _).trans (by norm_num)

/-- **`ker(1 - M(1,1,2)ᵀ) ≅ ℤ²`**, `x ↦ (x₀, x₁)`. -/
def kernelEquivC : (relationHom (graphMatrix ![1, 1, 2])).ker ≃+ (Fin 2 → ℤ) where
  toFun x := ![(x : Fin 3 → ℤ) 0, (x : Fin 3 → ℤ) 1]
  invFun y := ⟨![y 0, y 1, -y 0 - y 1], (mem_ker_relationHom_graphMatrix _ ne_zero_C _).2 (by
    rw [Fin.sum_univ_three]
    show y 0 + y 1 + (-y 0 - y 1) = 0
    ring)⟩
  left_inv x := by
    have h := (mem_ker_relationHom_graphMatrix _ ne_zero_C _).1 x.2
    rw [Fin.sum_univ_three] at h
    refine Subtype.ext (funext fun i => ?_)
    fin_cases i
    · rfl
    · rfl
    · show -(x : Fin 3 → ℤ) 0 - (x : Fin 3 → ℤ) 1 = (x : Fin 3 → ℤ) 2
      omega
  right_inv y := funext fun i => by fin_cases i <;> rfl
  map_add' x y := funext fun i => by fin_cases i <;> rfl

end C

end GraphCStar
end GroupApproximation
