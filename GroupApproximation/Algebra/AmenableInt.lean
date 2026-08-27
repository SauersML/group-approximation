import GroupApproximation.Algebra.AmenableMean
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The integers are amenable

The extension theorem of `Algebra.AmenableMean` reduces the manuscript's
"locally finite by `ℤ`" sentence to two inputs: the kernel is amenable,
which `Algebra.Amenable` supplies, and `ℤ` is amenable, which is this
file.

The mean is the Cesàro average along an ultrafilter: average a bounded
function over `{0, …, n-1}` and take the limit.  Invariance is the whole
content, and it is cheap for the *generator*, because the shifted and
unshifted sums telescope and differ only in two endpoint terms, so the
averages differ by `O(1/n)`.  Invariance for a generator upgrades to the
whole group because the elements under which a functional is invariant are
closed under multiplication and inverse.
-/

namespace GroupApproximation
namespace Amenability

open Filter Topology

/-! ## Invariance propagates along the group -/

variable {G : Type*} [Group G]

/-- If a functional is invariant under `g` and under `h`, it is invariant
under `g * h`. -/
theorem invariant_mul {eval : (G → ℝ) → ℝ} {g h : G}
    (hg : ∀ f : G → ℝ, IsBddFun f → eval (fun x ↦ f (g * x)) = eval f)
    (hh : ∀ f : G → ℝ, IsBddFun f → eval (fun x ↦ f (h * x)) = eval f)
    (f : G → ℝ) (hf : IsBddFun f) :
    eval (fun x ↦ f (g * h * x)) = eval f := by
  have hcomp : (fun x ↦ f (g * h * x)) = fun x ↦ (fun y ↦ f (g * y)) (h * x) := by
    funext x
    rw [mul_assoc]
  have hgf : IsBddFun (fun y ↦ f (g * y)) := by
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, fun y ↦ hC _⟩
  rw [hcomp, hh _ hgf, hg f hf]

/-- If a functional is invariant under `g`, it is invariant under `g⁻¹`. -/
theorem invariant_inv {eval : (G → ℝ) → ℝ} {g : G}
    (hg : ∀ f : G → ℝ, IsBddFun f → eval (fun x ↦ f (g * x)) = eval f)
    (f : G → ℝ) (hf : IsBddFun f) :
    eval (fun x ↦ f (g⁻¹ * x)) = eval f := by
  have hgf : IsBddFun (fun y ↦ f (g⁻¹ * y)) := by
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, fun y ↦ hC _⟩
  have h := hg (fun y ↦ f (g⁻¹ * y)) hgf
  simp only [← mul_assoc, inv_mul_cancel, one_mul] at h
  exact h.symm

/-! ## The Cesàro average -/

/-- The average of a function on `ℤ` over `{0, …, n-1}`. -/
noncomputable def intAvg (f : Multiplicative ℤ → ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n, f (Multiplicative.ofAdd (k : ℤ))) / (n : ℝ)

theorem intAvg_mem_Icc {f : Multiplicative ℤ → ℝ} {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (n : ℕ) : intAvg f n ∈ Set.Icc (-C) C := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 1)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [intAvg, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
      div_zero]
    exact ⟨neg_nonpos.mpr hC0, hC0⟩
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsum : |∑ k ∈ Finset.range n, f (Multiplicative.ofAdd (k : ℤ))| ≤
        (n : ℝ) * C := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ Finset.range n, |f (Multiplicative.ofAdd (k : ℤ))|
          ≤ ∑ _k ∈ Finset.range n, C := Finset.sum_le_sum fun k _ ↦ hC _
        _ = (n : ℝ) * C := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Set.mem_Icc, ← abs_le, intAvg, abs_div, abs_of_pos hnpos,
      div_le_iff₀ hnpos]
    calc |∑ k ∈ Finset.range n, f (Multiplicative.ofAdd (k : ℤ))|
        ≤ (n : ℝ) * C := hsum
      _ = C * (n : ℝ) := by ring

/-- Shifting by the generator changes the sum only in the endpoints. -/
theorem intAvg_shift_sum {f : Multiplicative ℤ → ℝ} (n : ℕ) :
    (∑ k ∈ Finset.range n,
        f (Multiplicative.ofAdd (1 : ℤ) * Multiplicative.ofAdd (k : ℤ))) -
      (∑ k ∈ Finset.range n, f (Multiplicative.ofAdd (k : ℤ))) =
    f (Multiplicative.ofAdd (n : ℤ)) - f (Multiplicative.ofAdd ((0 : ℕ) : ℤ)) := by
  have hstep : ∀ k : ℕ,
      f (Multiplicative.ofAdd (1 : ℤ) * Multiplicative.ofAdd (k : ℤ)) =
        f (Multiplicative.ofAdd (((k + 1 : ℕ)) : ℤ)) := by
    intro k
    congr 1
    show Multiplicative.ofAdd ((1 : ℤ) + (k : ℤ)) = _
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun k _ ↦ hstep k, ← Finset.sum_sub_distrib]
  exact Finset.sum_range_sub (fun k : ℕ ↦ f (Multiplicative.ofAdd (k : ℤ))) n

/-! ## The mean -/

/-- The Cesàro mean of a bounded function on `ℤ`, taken along a fixed
ultrafilter refining the eventually-large filter. -/
noncomputable def intEval (f : Multiplicative ℤ → ℝ) : ℝ := by
  classical
  exact if h : IsBddFun f then
    (exists_ultrafilter_tendsto_Icc (indexUltrafilter ℕ ⟨0⟩) (intAvg f)
      (intAvg_mem_Icc h.choose_spec)).choose
  else 0

theorem intEval_tendsto {f : Multiplicative ℤ → ℝ} (hf : IsBddFun f) :
    Tendsto (intAvg f) (indexUltrafilter ℕ ⟨0⟩) (nhds (intEval f)) := by
  classical
  rw [intEval, dif_pos hf]
  exact (exists_ultrafilter_tendsto_Icc (indexUltrafilter ℕ ⟨0⟩) (intAvg f)
    (intAvg_mem_Icc hf.choose_spec)).choose_spec.2

theorem intEval_add (f g : Multiplicative ℤ → ℝ) (hf : IsBddFun f)
    (hg : IsBddFun g) : intEval (f + g) = intEval f + intEval g := by
  refine tendsto_nhds_unique (intEval_tendsto (hf.add hg)) ?_
  have hsplit : intAvg (f + g) = fun n ↦ intAvg f n + intAvg g n := by
    funext n
    simp only [intAvg, Pi.add_apply]
    rw [Finset.sum_add_distrib, add_div]
  rw [hsplit]
  exact (intEval_tendsto hf).add (intEval_tendsto hg)

theorem intEval_nonneg (f : Multiplicative ℤ → ℝ) (hf : IsBddFun f)
    (hpos : ∀ x, 0 ≤ f x) : 0 ≤ intEval f := by
  refine ge_of_tendsto (intEval_tendsto hf) (Filter.Eventually.of_forall fun n ↦ ?_)
  refine div_nonneg (Finset.sum_nonneg fun k _ ↦ hpos _) (Nat.cast_nonneg n)

theorem intEval_const (c : ℝ) : intEval (fun _ ↦ c) = c := by
  refine tendsto_nhds_unique (intEval_tendsto (IsBddFun.const c)) ?_
  have hev : intAvg (fun _ : Multiplicative ℤ ↦ c) =ᶠ[(indexUltrafilter ℕ ⟨0⟩ : Filter ℕ)]
      fun _ ↦ c := by
    refine Filter.mem_of_superset
      (indexUltrafilter_le ⟨0⟩ (Filter.eventually_ge_atTop 1)) ?_
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := hn
      exact_mod_cast this
    show intAvg (fun _ ↦ c) n = c
    rw [intAvg, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_cancel_left₀ _ hnpos.ne']
  exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

theorem intEval_shift_one (f : Multiplicative ℤ → ℝ) (hf : IsBddFun f) :
    intEval (fun x ↦ f (Multiplicative.ofAdd (1 : ℤ) * x)) = intEval f := by
  obtain ⟨C, hC⟩ := hf
  have hshiftBdd : IsBddFun fun x ↦ f (Multiplicative.ofAdd (1 : ℤ) * x) :=
    ⟨C, fun x ↦ hC _⟩
  have hdiff : Tendsto
      (fun n ↦ intAvg (fun x ↦ f (Multiplicative.ofAdd (1 : ℤ) * x)) n - intAvg f n)
      atTop (nhds 0) := by
    have hbound : ∀ n : ℕ,
        |intAvg (fun x ↦ f (Multiplicative.ofAdd (1 : ℤ) * x)) n - intAvg f n| ≤
          (2 * C) / (n : ℝ) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [intAvg]
      · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        rw [intAvg, intAvg, div_sub_div_same, abs_div, abs_of_pos hnpos]
        gcongr
        rw [intAvg_shift_sum n]
        calc |f (Multiplicative.ofAdd (n : ℤ)) -
              f (Multiplicative.ofAdd (((0 : ℕ) : ℤ)))|
            ≤ |f (Multiplicative.ofAdd (n : ℤ))| +
                |f (Multiplicative.ofAdd (((0 : ℕ) : ℤ)))| := abs_sub _ _
          _ ≤ C + C := add_le_add (hC _) (hC _)
          _ = 2 * C := by ring
    have h0 : Tendsto (fun n : ℕ ↦ (2 * C) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (2 * C)
    have hneg : Tendsto (fun n : ℕ ↦ -((2 * C) / (n : ℝ))) atTop (nhds 0) := by
      simpa using h0.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg h0
      (fun n ↦ (abs_le.mp (hbound n)).1) (fun n ↦ (abs_le.mp (hbound n)).2)
  have hdiff' : Tendsto
      (fun n ↦ intAvg (fun x ↦ f (Multiplicative.ofAdd (1 : ℤ) * x)) n - intAvg f n)
      (indexUltrafilter ℕ ⟨0⟩) (nhds 0) :=
    hdiff.mono_left (indexUltrafilter_le ⟨0⟩)
  have hsum : Tendsto
      (fun n ↦ intAvg (fun x ↦ f (Multiplicative.ofAdd (1 : ℤ) * x)) n)
      (indexUltrafilter ℕ ⟨0⟩) (nhds (0 + intEval f)) := by
    have := hdiff'.add (intEval_tendsto ⟨C, hC⟩)
    simpa using this
  rw [zero_add] at hsum
  exact tendsto_nhds_unique (intEval_tendsto hshiftBdd) hsum

theorem intEval_invariant (g : Multiplicative ℤ) (f : Multiplicative ℤ → ℝ)
    (hf : IsBddFun f) : intEval (fun x ↦ f (g * x)) = intEval f := by
  have key : ∀ k : ℤ, ∀ f : Multiplicative ℤ → ℝ, IsBddFun f →
      intEval (fun x ↦ f (Multiplicative.ofAdd k * x)) = intEval f := by
    intro k
    induction k using Int.induction_on with
    | zero => intro f hf; simp
    | succ n ih =>
        intro f hf
        have hstep : (Multiplicative.ofAdd ((n : ℤ) + 1) : Multiplicative ℤ) =
            Multiplicative.ofAdd (n : ℤ) * Multiplicative.ofAdd (1 : ℤ) := rfl
        rw [hstep]
        exact invariant_mul (fun f hf ↦ ih f hf)
          (fun f hf ↦ intEval_shift_one f hf) f hf
    | pred n ih =>
        intro f hf
        have hstep : (Multiplicative.ofAdd (-(n : ℤ) - 1) : Multiplicative ℤ) =
            Multiplicative.ofAdd (-(n : ℤ)) * (Multiplicative.ofAdd (1 : ℤ))⁻¹ := by
          show Multiplicative.ofAdd (-(n : ℤ) - 1) =
            Multiplicative.ofAdd (-(n : ℤ) + -(1 : ℤ))
          congr 1
        rw [hstep]
        exact invariant_mul (fun f hf ↦ ih f hf)
          (fun f hf ↦ invariant_inv (fun f hf ↦ intEval_shift_one f hf) f hf) f hf
  have hg : g = Multiplicative.ofAdd (Multiplicative.toAdd g) := rfl
  rw [hg]
  exact key _ f hf

/-- **The integers are amenable.** -/
noncomputable def intFunctionMean : FunctionMean (Multiplicative ℤ) where
  eval := intEval
  eval_add := intEval_add
  eval_nonneg := intEval_nonneg
  eval_const := intEval_const
  eval_invariant := intEval_invariant

theorem hasInvariantMean_int : HasInvariantMean (Multiplicative ℤ) :=
  ⟨intFunctionMean⟩

end Amenability
end GroupApproximation
