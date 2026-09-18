import GroupApproximation.Leavitt.LeavittNormalForm
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The length grading of `L_k(1,2)`

Ingredient of `binaryLeavitt_idempotent_dichotomy` (manuscript
`simple_kazhdan_sofic_group.tex`, l.733-735, `sec:questions`, question Q2:
the low `K`-theory of the binary Leavitt algebra).

The substitution `s_i ↦ s_i X`, `t_i ↦ t_i X⁻¹` defines a Leavitt family in
the Laurent algebra `L[ℤ] = AddMonoidAlgebra L ℤ` over `L = L_k(1,2)`, hence
an algebra map `grade : L →ₐ[k] L[ℤ]`.  Setting `X = 1` collapses it back:
`collapse ∘ grade = id`.  An `s`-word of length `n` is sent to the single
term in degree `n`.  Nothing here uses a basis of `L_k(1,2)`.
-/

namespace GroupApproximation.Full.LVLowKZeroCore

open GroupApproximation.BinaryLeavitt

noncomputable section

variable (k : Type) [Field k]

/-- The graded Leavitt family `s_i X`, `t_i X⁻¹` in `L[ℤ]`. -/
def gradedFamily : LeavittFamily (AddMonoidAlgebra (BinaryLeavittAlgebra k) ℤ) where
  s0 := AddMonoidAlgebra.single 1 (family k).s0
  s1 := AddMonoidAlgebra.single 1 (family k).s1
  t0 := AddMonoidAlgebra.single (-1) (family k).t0
  t1 := AddMonoidAlgebra.single (-1) (family k).t1
  t0_s0 := by
    rw [AddMonoidAlgebra.single_mul_single, (family k).t0_s0, neg_add_cancel,
      AddMonoidAlgebra.one_def]
  t0_s1 := by
    rw [AddMonoidAlgebra.single_mul_single, (family k).t0_s1,
      AddMonoidAlgebra.single_zero]
  t1_s0 := by
    rw [AddMonoidAlgebra.single_mul_single, (family k).t1_s0,
      AddMonoidAlgebra.single_zero]
  t1_s1 := by
    rw [AddMonoidAlgebra.single_mul_single, (family k).t1_s1, neg_add_cancel,
      AddMonoidAlgebra.one_def]
  sum_range := by
    rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single,
      ← AddMonoidAlgebra.single_add, (family k).sum_range, add_neg_cancel,
      AddMonoidAlgebra.one_def]

/-- The length grading `L_k(1,2) → L_k(1,2)[ℤ]`. -/
def grade : BinaryLeavittAlgebra k →ₐ[k] AddMonoidAlgebra (BinaryLeavittAlgebra k) ℤ :=
  BinaryLeavitt.lift (gradedFamily k)

/-- Evaluation at `X = 1`. -/
def collapse : AddMonoidAlgebra (BinaryLeavittAlgebra k) ℤ →ₐ[k] BinaryLeavittAlgebra k :=
  AddMonoidAlgebra.liftNCAlgHom (AlgHom.id k (BinaryLeavittAlgebra k)) 1
    (fun _ _ => Commute.one_right _)

theorem collapse_single (d : ℤ) (x : BinaryLeavittAlgebra k) :
    collapse k (AddMonoidAlgebra.single d x) = x := by
  simp [collapse]

/-- `collapse ∘ grade = id`: the grading is faithful. -/
theorem collapse_grade (x : BinaryLeavittAlgebra k) : collapse k (grade k x) = x := by
  have h : (collapse k).comp (grade k) = AlgHom.id k (BinaryLeavittAlgebra k) := by
    refine AlgHom.ext_of_adjoin_eq_top (adjoin_range_generator k) ?_
    rintro _ ⟨g, rfl⟩
    show collapse k (BinaryLeavitt.lift (gradedFamily k) (generator k g)) = generator k g
    rw [lift_generator]
    fin_cases g
    · exact collapse_single k 1 (generator k BinaryLeavitt.s0)
    · exact collapse_single k 1 (generator k BinaryLeavitt.s1)
    · exact collapse_single k (-1) (generator k BinaryLeavitt.t0)
    · exact collapse_single k (-1) (generator k BinaryLeavitt.t1)
  exact DFunLike.congr_fun h x

theorem grade_ne_zero {x : BinaryLeavittAlgebra k} (hx : x ≠ 0) : grade k x ≠ 0 := by
  intro h
  apply hx
  rw [← collapse_grade k x, h, map_zero]

theorem grade_s (i : Fin 2) :
    grade k ((family k).s i) = AddMonoidAlgebra.single 1 ((family k).s i) := by
  fin_cases i
  · exact lift_generator (k := k) (gradedFamily k) BinaryLeavitt.s0
  · exact lift_generator (k := k) (gradedFamily k) BinaryLeavitt.s1

/-- An `s`-word of length `n` is homogeneous of degree `n`. -/
theorem grade_wordS (a : List (Fin 2)) :
    grade k ((family k).wordS a) =
      AddMonoidAlgebra.single (a.length : ℤ) ((family k).wordS a) := by
  induction a with
  | nil =>
      rw [LeavittFamily.wordS_nil, map_one, List.length_nil, Nat.cast_zero,
        AddMonoidAlgebra.one_def]
  | cons i a ih =>
      rw [LeavittFamily.wordS_cons, map_mul, grade_s, ih,
        AddMonoidAlgebra.single_mul_single, List.length_cons, Nat.cast_add, Nat.cast_one,
        add_comm]

/-- If `x` vanishes below degree `d₀` and `y` vanishes in degrees `≤ 0`, then
`x * y` vanishes in degree `d₀`. -/
theorem coeff_mul_eq_zero_of_lt {R : Type*} [Semiring R] (x y : AddMonoidAlgebra R ℤ)
    (d₀ : ℤ) (hx : ∀ d : ℤ, d < d₀ → x.coeff d = 0)
    (hy : ∀ d : ℤ, d ≤ 0 → y.coeff d = 0) :
    (x * y).coeff d₀ = 0 := by
  rw [AddMonoidAlgebra.coeff_mul]
  refine Finset.sum_eq_zero ?_
  intro m₁ hm₁
  refine Finset.sum_eq_zero ?_
  intro m₂ hm₂
  refine if_neg ?_
  have h₁ : d₀ ≤ m₁ := not_lt.mp fun h => (Finsupp.mem_support_iff.mp hm₁) (hx m₁ h)
  have h₂ : 0 < m₂ := not_le.mp fun h => (Finsupp.mem_support_iff.mp hm₂) (hy m₂ h)
  omega

/-- The degree-zero coefficient, as a `k`-linear map `L → L`. -/
def coeffZero : BinaryLeavittAlgebra k →ₗ[k] BinaryLeavittAlgebra k where
  toFun x := (grade k x).coeff 0
  map_add' x y := by
    show (grade k (x + y)).coeff 0 = (grade k x).coeff 0 + (grade k y).coeff 0
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' c x := by
    show (grade k (c • x)).coeff 0 = (RingHom.id k) c • (grade k x).coeff 0
    rw [map_smul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, RingHom.id_apply]

theorem coeffZero_apply (x : BinaryLeavittAlgebra k) :
    coeffZero k x = (grade k x).coeff 0 := rfl

theorem coeffZero_one : coeffZero k 1 = 1 := by
  rw [coeffZero_apply, map_one, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same]

theorem coeffZero_wordS_cons (i : Fin 2) (a : List (Fin 2)) :
    coeffZero k ((family k).wordS (i :: a)) = 0 := by
  rw [coeffZero_apply, grade_wordS, AddMonoidAlgebra.coeff_single]
  refine Finsupp.single_eq_of_ne ?_
  rw [List.length_cons]
  omega

end

end GroupApproximation.Full.LVLowKZeroCore
