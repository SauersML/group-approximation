import GroupApproximation.Leavitt.AryWindowReduction
import GroupApproximation.KOne.VandermondeExtraction
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Data.Int.Interval
import GroupApproximation.Meta.AxiomGuard

/-!
# Graded components of `L_k(1,d)`

The binary development separates degree components with a scaled faithful stream
representation (`KOne/ScaledStreamRepresentation.lean`, `KOne/GradedIndependence.lean`,
`KOne/BaseChangeIndependence.lean`).  At arity `d` the universal property of the
presented algebra gives the scaling directly, with no representation at all:

* for a unit `c` of the ground field, `(c • sᵢ, c⁻¹ • tᵢ)` is again a `d`-ary Leavitt
  family (`CompleteMatrixFamily.scaled`), so `AryLeavitt.lift` of it is an algebra
  endomorphism `scale c` of `L_k(1,d)` multiplying a degree-`n` element by `c^n`;
* over an infinite field the Vandermonde extraction then kills each component of a
  vanishing sum of pure-degree elements (`graded_independence_of_infinite`);
* over an arbitrary field, base change to `k(X)` is injective by simplicity and carries
  degree windows to degree windows (`graded_independence`).

Every window element is a finite sum of pure-degree components (`exists_components`,
for any family), and at `L_k(1,d)` the decomposition is unique (`components_unique`).
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

section Scaled

variable {k : Type*} [Field k] [Algebra k A]

/-- The gauge-rescaled family `(c • sᵢ, c⁻¹ • tᵢ)`. -/
def scaled (c : kˣ) : CompleteMatrixFamily A ι where
  left i := (c : k) • F.left i
  right i := ((c⁻¹ : kˣ) : k) • F.right i
  orthogonal i j := by
    rw [smul_mul_smul_comm, Units.inv_mul, one_smul, F.orthogonal]
  complete := by
    simp only [smul_mul_smul_comm, Units.mul_inv, one_smul]
    exact F.complete

@[simp] theorem scaled_left (c : kˣ) (i : ι) :
    (F.scaled c).left i = (c : k) • F.left i := rfl

@[simp] theorem scaled_right (c : kˣ) (i : ι) :
    (F.scaled c).right i = ((c⁻¹ : kˣ) : k) • F.right i := rfl

theorem scaled_wordS (c : kˣ) (a : List ι) :
    (F.scaled c).wordS a = (c : k) ^ a.length • F.wordS a := by
  induction a with
  | nil => simp
  | cons i a ih =>
      rw [wordS_cons, wordS_cons, ih, scaled_left, smul_mul_smul_comm,
        List.length_cons, pow_succ']

theorem scaled_wordT (c : kˣ) (b : List ι) :
    (F.scaled c).wordT b = ((c⁻¹ : kˣ) : k) ^ b.length • F.wordT b := by
  induction b with
  | nil => simp
  | cons i b ih =>
      rw [wordT_cons, wordT_cons, ih, scaled_right, smul_mul_smul_comm,
        List.length_cons, pow_succ]

end Scaled

section Components

variable {k : Type*} [Field k] [Algebra k A]

/-- **Graded decomposition**: every window element is a finite sum of pure-degree
components supported in the window. -/
theorem exists_components {lo hi : ℤ} {x : A}
    (hx : x ∈ Submodule.span k (F.degreeMonomials lo hi)) :
    ∃ y : ℤ → A,
      (∀ n, y n ∈ Submodule.span k (F.degreeMonomials n n)) ∧
      (∀ n, n < lo ∨ hi < n → y n = 0) ∧
      x = ∑ n ∈ Finset.Icc lo hi, y n := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      refine ⟨fun n ↦ if n = (a.length : ℤ) - b.length then
        F.wordS a * F.wordT b else 0, ?_, ?_, ?_⟩
      · intro n
        beta_reduce
        by_cases hn : n = (a.length : ℤ) - b.length
        · rw [if_pos hn]
          exact Submodule.subset_span ⟨a, b, by omega, by omega, rfl⟩
        · rw [if_neg hn]
          exact Submodule.zero_mem _
      · intro n hn
        beta_reduce
        rw [if_neg (show ¬n = (a.length : ℤ) - b.length from by omega)]
      · refine ((Finset.sum_eq_single ((a.length : ℤ) - b.length)
          (fun n _ hn ↦ if_neg hn)
          (fun hn₀ ↦ absurd (Finset.mem_Icc.mpr ⟨hl, hh⟩)
            hn₀)).trans (if_pos rfl)).symm
  | zero =>
      exact ⟨0, fun n ↦ Submodule.zero_mem _, fun n _ ↦ rfl, by simp⟩
  | add x₁ x₂ _ _ h₁ h₂ =>
      obtain ⟨y₁, hy₁, hz₁, hs₁⟩ := h₁
      obtain ⟨y₂, hy₂, hz₂, hs₂⟩ := h₂
      refine ⟨y₁ + y₂, fun n ↦ Submodule.add_mem _ (hy₁ n) (hy₂ n),
        fun n hn ↦ ?_, ?_⟩
      · show y₁ n + y₂ n = 0
        rw [hz₁ n hn, hz₂ n hn, add_zero]
      · rw [hs₁, hs₂, ← Finset.sum_add_distrib]
        rfl
  | smul r x _ h =>
      obtain ⟨y, hy, hz, hs⟩ := h
      refine ⟨r • y, fun n ↦ Submodule.smul_mem _ _ (hy n),
        fun n hn ↦ ?_, ?_⟩
      · show r • y n = 0
        rw [hz n hn, smul_zero]
      · rw [hs, Finset.smul_sum]
        rfl

end Components

end CompleteMatrixFamily

namespace AryLeavitt

open CompleteMatrixFamily

variable (k : Type) [Field k] (d : ℕ)

/-- `lift` carries the `s`-words of the canonical family to those of the target family. -/
theorem lift_wordS {A : Type*} [Ring A] [Algebra k A]
    (F : CompleteMatrixFamily A (Fin d)) (a : List (Fin d)) :
    lift (k := k) F ((family k d).wordS a) = F.wordS a := by
  induction a with
  | nil => simp
  | cons i a ih =>
      rw [wordS_cons, wordS_cons, map_mul, ih,
        show (family k d).left i = genS k d i from rfl, lift_genS]

/-- `lift` carries the `t`-words of the canonical family to those of the target family. -/
theorem lift_wordT {A : Type*} [Ring A] [Algebra k A]
    (F : CompleteMatrixFamily A (Fin d)) (b : List (Fin d)) :
    lift (k := k) F ((family k d).wordT b) = F.wordT b := by
  induction b with
  | nil => simp
  | cons i b ih =>
      rw [wordT_cons, wordT_cons, map_mul, ih,
        show (family k d).right i = genT k d i from rfl, lift_genT]

/-- **The gauge endomorphism** `sᵢ ↦ c • sᵢ`, `tᵢ ↦ c⁻¹ • tᵢ` of `L_k(1,d)`. -/
noncomputable def scale (c : kˣ) : AryLeavittAlgebra k d →ₐ[k] AryLeavittAlgebra k d :=
  lift ((family k d).scaled c)

theorem scale_monomial (c : kˣ) (a b : List (Fin d)) :
    scale k d c ((family k d).wordS a * (family k d).wordT b) =
      ((c : k) ^ a.length * ((c⁻¹ : kˣ) : k) ^ b.length) •
        ((family k d).wordS a * (family k d).wordT b) := by
  rw [scale, map_mul, lift_wordS, lift_wordT, scaled_wordS, scaled_wordT,
    smul_mul_smul_comm]

/-- **Degree scaling**: on the span of degree-`n` monomials the gauge endomorphism is
multiplication by `c^n`. -/
theorem scale_of_mem_degree (c : kˣ) {n : ℤ} {x : AryLeavittAlgebra k d}
    (hx : x ∈ Submodule.span k ((family k d).degreeMonomials n n)) :
    scale k d c x = ((c ^ n : kˣ) : k) • x := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      rw [scale_monomial]
      congr 1
      have hn : n = (a.length : ℤ) - b.length := by omega
      rw [hn, zpow_sub, zpow_natCast, zpow_natCast, ← inv_pow, Units.val_mul,
        Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul r x _ hx => rw [map_smul, hx, smul_comm]

/-- **Graded independence over an infinite field**: a vanishing finite sum of
pure-degree elements of `L_k(1,d)` has all components zero. -/
theorem graded_independence_of_infinite [Infinite k] (D : Finset ℤ)
    (x : ℤ → AryLeavittAlgebra k d)
    (hx : ∀ n ∈ D, x n ∈ Submodule.span k ((family k d).degreeMonomials n n))
    (hsum : ∑ n ∈ D, x n = 0) : ∀ n ∈ D, x n = 0 := by
  refine eq_zero_of_forall_units_zpow_smul (K := k) (V := AryLeavittAlgebra k d) D x ?_
  intro c
  have h1 := congrArg (scale k d c) hsum
  rw [map_sum, map_zero] at h1
  rw [← h1]
  exact Finset.sum_congr rfl fun n hn ↦ (scale_of_mem_degree k d c (hx n hn)).symm

/-! ### Base change to the rational function field -/

/-- Coefficient extension along `k → k(X)`. -/
noncomputable def baseChange :
    AryLeavittAlgebra k d →ₐ[k] AryLeavittAlgebra (RatFunc k) d :=
  lift (family (RatFunc k) d)

theorem baseChange_wordS (a : List (Fin d)) :
    baseChange k d ((family k d).wordS a) = (family (RatFunc k) d).wordS a :=
  lift_wordS k d (family (RatFunc k) d) a

theorem baseChange_wordT (b : List (Fin d)) :
    baseChange k d ((family k d).wordT b) = (family (RatFunc k) d).wordT b :=
  lift_wordT k d (family (RatFunc k) d) b

/-- Base change is injective, by simplicity of the source. -/
theorem baseChange_injective (hd : 2 ≤ d) : Function.Injective (baseChange k d) := by
  haveI : NeZero d := ⟨by omega⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  obtain ⟨p, q, hpq⟩ := exists_mul_mul_eq_one k d hd hne
  have h1 := congrArg (baseChange k d) hpq
  rw [map_mul, map_mul, hx, mul_zero, zero_mul, map_one] at h1
  exact zero_ne_one h1

/-- Base change carries degree windows to degree windows. -/
theorem baseChange_mem_span_degree {lo hi : ℤ} {x : AryLeavittAlgebra k d}
    (hx : x ∈ Submodule.span k ((family k d).degreeMonomials lo hi)) :
    baseChange k d x ∈ Submodule.span (RatFunc k)
      ((family (RatFunc k) d).degreeMonomials lo hi) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      rw [map_mul, baseChange_wordS, baseChange_wordT]
      exact Submodule.subset_span ⟨a, b, hl, hh, rfl⟩
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
      rw [map_smul, ← algebraMap_smul (RatFunc k) r (baseChange k d x)]
      exact Submodule.smul_mem _ _ hx

/-- **Graded independence over every field**: a vanishing finite sum of pure-degree
elements of `L_k(1,d)` has all components zero. -/
theorem graded_independence (hd : 2 ≤ d) (D : Finset ℤ)
    (x : ℤ → AryLeavittAlgebra k d)
    (hx : ∀ n ∈ D, x n ∈ Submodule.span k ((family k d).degreeMonomials n n))
    (hsum : ∑ n ∈ D, x n = 0) : ∀ n ∈ D, x n = 0 := by
  haveI : Infinite (RatFunc k) :=
    Infinite.of_injective (algebraMap (Polynomial k) (RatFunc k))
      (IsFractionRing.injective _ _)
  have hker := graded_independence_of_infinite (RatFunc k) d D
    (fun n ↦ baseChange k d (x n))
    (fun n hn ↦ baseChange_mem_span_degree k d (hx n hn))
    (by rw [← map_sum, hsum, map_zero])
  intro n hn
  apply baseChange_injective k d hd
  rw [map_zero]
  exact hker n hn

/-- **Uniqueness of components** in `L_k(1,d)`: two componentwise decompositions of the
same element agree degreewise. -/
theorem components_unique (hd : 2 ≤ d) {D : Finset ℤ}
    {y z : ℤ → AryLeavittAlgebra k d}
    (hy : ∀ n ∈ D, y n ∈ Submodule.span k ((family k d).degreeMonomials n n))
    (hz : ∀ n ∈ D, z n ∈ Submodule.span k ((family k d).degreeMonomials n n))
    (hsum : ∑ n ∈ D, y n = ∑ n ∈ D, z n) :
    ∀ n ∈ D, y n = z n := by
  have hind := graded_independence k d hd D (fun n ↦ y n - z n)
    (fun n hn ↦ Submodule.sub_mem _ (hy n hn) (hz n hn))
    (by rw [Finset.sum_sub_distrib, hsum, sub_self])
  intro n hn
  exact sub_eq_zero.mp (hind n hn)

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.scaled_wordS
#audit_axioms GroupApproximation.CompleteMatrixFamily.scaled_wordT
#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_components
#audit_axioms GroupApproximation.AryLeavitt.scale_of_mem_degree
#audit_axioms GroupApproximation.AryLeavitt.graded_independence_of_infinite
#audit_axioms GroupApproximation.AryLeavitt.baseChange_injective
#audit_axioms GroupApproximation.AryLeavitt.graded_independence
#audit_axioms GroupApproximation.AryLeavitt.components_unique
