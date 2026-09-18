import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapClosureData
import Mathlib.Analysis.CStarAlgebra.lpSpace

/-!
# Countable `c₀`-sums of separable non-unital C⋆-algebras

For a sequence `E n` of normed groups, the norm-null sequences form a closed subset `c0Set E` of
`lp E ∞`.  When every `E n` is separable this set is separable: the finite truncations
`truncate N x` (the first `N` coordinates, padded by zero) are dense in it, and each space of
truncations is a continuous image of the separable finite product `∀ n : Fin N, E n`.

For C⋆-algebras `E n` the norm-null sequences are a closed non-unital `⋆`-subalgebra
`c0Subalgebra E` of the C⋆-algebra `lp E ∞`; this is the C⋆-direct sum `⊕ₙ E n`.  It is bundled
as `SepNUCStarAlgebra.c0Sum`, with `IsCommutative.c0Sum`.

This is the algebra `⊕ₙ Aₙ` receiving the mapping telescope of an inductive system (Blackadar,
*K-Theory for Operator Algebras*, 21.5 and 22.3.4), which is the input of the inductive-limit
closure of the Rosenberg--Schochet class used for the UCT input of `thm:fixed-radical-membership`
in `non_mf_group_notes.tex`.
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap.InductiveLimit

open Filter Topology
open scoped ENNReal

noncomputable section

/-- An eventual bound from convergence to `0`. -/
theorem exists_lt_of_tendsto_zero {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) {ε : ℝ}
    (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → u n < ε := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hu ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [Real.dist_eq, sub_zero] at h
  exact lt_of_le_of_lt (le_abs_self (u n)) h

section Normed

variable {F : ℕ → Type} [∀ n, NormedAddCommGroup (F n)]

/-- The norm-null sequences inside `lp F ∞`. -/
def c0Set (F : ℕ → Type) [∀ n, NormedAddCommGroup (F n)] : Set (lp F ∞) :=
  {f | Tendsto (fun n => ‖f n‖) atTop (𝓝 0)}

/-- The set of norm-null sequences is closed in `lp F ∞`. -/
theorem isClosed_c0Set : IsClosed (c0Set F) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  show Tendsto (fun n => ‖f n‖) atTop (𝓝 0)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 2) (half_pos hε)
  have hg' : Tendsto (fun n => ‖g n‖) atTop (𝓝 0) := hg
  obtain ⟨N, hN⟩ := exists_lt_of_tendsto_zero hg' (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have h1 : ‖f n - g n‖ ≤ ‖f - g‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero (f - g) n
  have h2 : ‖f n‖ - ‖g n‖ ≤ ‖f n - g n‖ := norm_sub_norm_le (f n) (g n)
  have h3 : ‖f - g‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact hfg
  have h4 : ‖g n‖ < ε / 2 := hN n hn
  linarith

/-- The first `N` coordinates of a sequence, padded by zero. -/
def truncate (N : ℕ) (x : ∀ n : Fin N, F n) : lp F ∞ :=
  ⟨fun n => if h : n < N then x ⟨n, h⟩ else 0, by
    refine memℓp_infty_iff.2 ⟨‖x‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    by_cases h : n < N
    · simp only [dif_pos h]
      exact norm_le_pi_norm x ⟨n, h⟩
    · simp only [dif_neg h, norm_zero]
      exact norm_nonneg x⟩

theorem truncate_apply_of_lt {N n : ℕ} (x : ∀ n : Fin N, F n) (h : n < N) :
    truncate N x n = x ⟨n, h⟩ := by
  show (if h' : n < N then x ⟨n, h'⟩ else 0) = x ⟨n, h⟩
  rw [dif_pos h]

theorem truncate_apply_of_not_lt {N n : ℕ} (x : ∀ n : Fin N, F n) (h : ¬n < N) :
    truncate N x n = 0 := by
  show (if h' : n < N then x ⟨n, h'⟩ else 0) = 0
  rw [dif_neg h]

/-- Truncation is `1`-Lipschitz, hence continuous. -/
theorem continuous_truncate (N : ℕ) : Continuous (truncate (F := F) N) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  refine lp.norm_le_of_forall_le (norm_nonneg _) fun n => ?_
  have hsub : (truncate N x - truncate N y) n = truncate N x n - truncate N y n := rfl
  rw [hsub]
  by_cases h : n < N
  · rw [truncate_apply_of_lt x h, truncate_apply_of_lt y h]
    exact norm_le_pi_norm (x - y) ⟨n, h⟩
  · rw [truncate_apply_of_not_lt x h, truncate_apply_of_not_lt y h, sub_zero, norm_zero]
    exact norm_nonneg _

/-- Every norm-null sequence is a limit of truncations. -/
theorem c0Set_subset_closure_truncate :
    c0Set F ⊆ closure (⋃ N : ℕ, Set.range (truncate (F := F) N)) := by
  intro f hf
  have hf' : Tendsto (fun n => ‖f n‖) atTop (𝓝 0) := hf
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_lt_of_tendsto_zero hf' (half_pos hε)
  refine ⟨truncate N fun n => f n.1, Set.mem_iUnion.2 ⟨N, ⟨fun n => f n.1, rfl⟩⟩, ?_⟩
  rw [dist_eq_norm]
  have hle : ‖f - truncate N fun n => f n.1‖ ≤ ε / 2 := by
    refine lp.norm_le_of_forall_le (half_pos hε).le fun n => ?_
    have hsub : (f - truncate N fun n => f n.1) n = f n - truncate N (fun n => f n.1) n := rfl
    rw [hsub]
    by_cases h : n < N
    · rw [truncate_apply_of_lt _ h, sub_self, norm_zero]
      exact (half_pos hε).le
    · rw [truncate_apply_of_not_lt _ h, sub_zero]
      exact (hN n (Nat.le_of_not_lt h)).le
  linarith

/-- **The norm-null sequences of separable spaces form a separable set.** -/
theorem isSeparable_c0Set [∀ n, TopologicalSpace.SeparableSpace (F n)] :
    TopologicalSpace.IsSeparable (c0Set F) := by
  have hunion : TopologicalSpace.IsSeparable (⋃ N : ℕ, Set.range (truncate (F := F) N)) :=
    TopologicalSpace.IsSeparable.iUnion fun N =>
      TopologicalSpace.isSeparable_range (continuous_truncate N)
  exact hunion.closure.mono c0Set_subset_closure_truncate

end Normed

section Algebra

variable (E : ℕ → Type) [∀ n, NonUnitalCStarAlgebra (E n)]

/-- **The C⋆-direct sum** `⊕ₙ E n`: norm-null sequences, a non-unital `⋆`-subalgebra of
`lp E ∞`. -/
def c0Subalgebra : NonUnitalStarSubalgebra ℂ (lp E ∞) where
  carrier := c0Set E
  add_mem' := fun {f g} hf hg => by
    have hf' : Tendsto (fun n => ‖f n‖) atTop (𝓝 0) := hf
    have hg' : Tendsto (fun n => ‖g n‖) atTop (𝓝 0) := hg
    have hsum : Tendsto (fun n => ‖f n‖ + ‖g n‖) atTop (𝓝 0) := by
      have h := hf'.add hg'
      rw [add_zero] at h
      exact h
    show Tendsto (fun n => ‖(f + g) n‖) atTop (𝓝 0)
    exact squeeze_zero (fun n => norm_nonneg ((f + g) n))
      (fun n => norm_add_le (f n) (g n)) hsum
  zero_mem' := by
    show Tendsto (fun n => ‖(0 : lp E ∞) n‖) atTop (𝓝 0)
    have h0 : (fun n => ‖(0 : lp E ∞) n‖) = fun _ => (0 : ℝ) := by
      funext n
      show ‖(0 : E n)‖ = 0
      exact norm_zero
    rw [h0]
    exact tendsto_const_nhds
  mul_mem' := fun {f g} hf _ => by
    have hf' : Tendsto (fun n => ‖f n‖) atTop (𝓝 0) := hf
    have hprod : Tendsto (fun n => ‖f n‖ * ‖g‖) atTop (𝓝 0) := by
      have h := hf'.mul_const ‖g‖
      rw [zero_mul] at h
      exact h
    show Tendsto (fun n => ‖(f * g) n‖) atTop (𝓝 0)
    refine squeeze_zero (fun n => norm_nonneg ((f * g) n)) (fun n => ?_) hprod
    calc ‖(f * g) n‖ = ‖f n * g n‖ := rfl
      _ ≤ ‖f n‖ * ‖g n‖ := norm_mul_le (f n) (g n)
      _ ≤ ‖f n‖ * ‖g‖ :=
        mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero g n)
          (norm_nonneg _)
  smul_mem' := fun c {f} hf => by
    have hf' : Tendsto (fun n => ‖f n‖) atTop (𝓝 0) := hf
    have hprod : Tendsto (fun n => ‖c‖ * ‖f n‖) atTop (𝓝 0) := by
      have h := hf'.const_mul ‖c‖
      rw [mul_zero] at h
      exact h
    show Tendsto (fun n => ‖(c • f) n‖) atTop (𝓝 0)
    have heq : (fun n => ‖(c • f) n‖) = fun n => ‖c‖ * ‖f n‖ := by
      funext n
      show ‖c • f n‖ = ‖c‖ * ‖f n‖
      exact norm_smul c (f n)
    rw [heq]
    exact hprod
  star_mem' := fun {f} hf => by
    have hf' : Tendsto (fun n => ‖f n‖) atTop (𝓝 0) := hf
    show Tendsto (fun n => ‖(star f) n‖) atTop (𝓝 0)
    have heq : (fun n => ‖(star f) n‖) = fun n => ‖f n‖ := by
      funext n
      show ‖star (f n)‖ = ‖f n‖
      exact norm_star (f n)
    rw [heq]
    exact hf'

theorem mem_c0Subalgebra {f : lp E ∞} :
    f ∈ c0Subalgebra E ↔ Tendsto (fun n => ‖f n‖) atTop (𝓝 0) :=
  Iff.rfl

theorem isClosed_c0Subalgebra : IsClosed ((c0Subalgebra E : Set (lp E ∞))) :=
  isClosed_c0Set

/-- The direct sum is a C⋆-algebra. -/
instance c0Subalgebra.nonUnitalCStarAlgebra : NonUnitalCStarAlgebra (c0Subalgebra E) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra _ (h_closed := isClosed_c0Subalgebra E)

/-- A separable subset of `lp E ∞` inside the norm-null sequences carries a separable subtype. -/
theorem separableSpace_of_subset_c0Set [∀ n, TopologicalSpace.SeparableSpace (E n)]
    {s : Set (lp E ∞)} (hs : s ⊆ c0Set E) : TopologicalSpace.SeparableSpace s :=
  (isSeparable_c0Set.mono hs).separableSpace

instance c0Subalgebra.separableSpace [∀ n, TopologicalSpace.SeparableSpace (E n)] :
    TopologicalSpace.SeparableSpace (c0Subalgebra E) :=
  separableSpace_of_subset_c0Set E (s := (c0Subalgebra E : Set (lp E ∞))) le_rfl

end Algebra

end

end GroupApproximation.Full.TWWUCT.Bootstrap.InductiveLimit

namespace GroupApproximation.Full.TWWUCT.Bootstrap

open GroupApproximation.Full.TWWUCT.Bootstrap.InductiveLimit

noncomputable section

/-- **The countable C⋆-direct sum** `⊕ₙ A n` of separable non-unital C⋆-algebras. -/
def SepNUCStarAlgebra.c0Sum (A : ℕ → SepNUCStarAlgebra) : SepNUCStarAlgebra where
  carrier := c0Subalgebra fun n => (A n : Type)

/-- A direct sum of commutative algebras is commutative. -/
theorem SepNUCStarAlgebra.IsCommutative.c0Sum {A : ℕ → SepNUCStarAlgebra}
    (hA : ∀ n, (A n).IsCommutative) : (SepNUCStarAlgebra.c0Sum A).IsCommutative := by
  intro x y
  refine Subtype.ext (lp.ext ?_)
  funext n
  exact hA n (x.1 n) (y.1 n)

end

end GroupApproximation.Full.TWWUCT.Bootstrap
