import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Analysis.STW22TypeIC0Sum

/-!
# The countable C-star `c₀`-direct sum

For a family of unital C-star algebras `D n`, this file constructs the genuine
nonunital C-star algebra

`C0DirectSum D = {x ∈ ∏∞ D n | ‖x n‖ → 0}`.

It also constructs the coordinate summand inclusions and proves, without an
abstract input bundle, the two properties consumed by `STW22TypeIC0Sum`:

* each coordinate range is a two-sided ideal;
* a representation which kills every coordinate summand kills the whole
  `c₀`-sum.

The second statement is proved by explicit finite truncations converging in
the supremum norm.
-/

namespace GroupApproximation
namespace CStarC0DirectSum

open Filter Topology PolarLiftingGeneralCStar
open STW22
open scoped ENNReal

noncomputable section

universe u v

variable (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-- The norm-null sequences, as a nonunital star subalgebra of the bounded
product. -/
def c0StarSubalgebra :
    NonUnitalStarSubalgebra ℂ (BoundedCStarSequence D) where
  carrier := nullCStarSequenceIdeal D atTop
  zero_mem' := (nullCStarSequenceIdeal D atTop).zero_mem
  add_mem' := (nullCStarSequenceIdeal D atTop).add_mem
  mul_mem' := fun _ hb ↦
    (nullCStarSequenceIdeal D atTop).mul_mem_left _ hb
  smul_mem' := fun c x hx ↦ by
    change IsNullCStarSequence D atTop (c • x)
    change IsNullCStarSequence D atTop x at hx
    simpa [IsNullCStarSequence, norm_smul] using
      tendsto_const_nhds.mul hx
  star_mem' := nullCStarSequenceIdeal_star_mem D atTop

noncomputable instance c0StarSubalgebra_isClosed :
    IsClosed (c0StarSubalgebra D : Set (BoundedCStarSequence D)) :=
  isClosed_nullCStarSequenceIdeal D atTop

/-- The countable nonunital C-star direct sum `⨁ₙ^{c₀} D n`. -/
abbrev C0DirectSum := ↥(c0StarSubalgebra D)

noncomputable instance c0DirectSum_nonUnitalCStarAlgebra :
    NonUnitalCStarAlgebra (C0DirectSum D) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (c0StarSubalgebra D)

/-- Put one block element in coordinate `n` and zero in every other
coordinate. -/
def summandInclusion (n : ℕ) : D n →⋆ₙₐ[ℂ] C0DirectSum D where
  toFun x := ⟨lp.single ∞ n x, by
    change IsNullCStarSequence D atTop _
    rw [IsNullCStarSequence, Metric.tendsto_atTop]
    intro ε hε
    refine ⟨n + 1, fun m hm ↦ ?_⟩
    have hmn : m ≠ n :=
      Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self n) hm)
    rw [Real.dist_eq, sub_zero, abs_norm,
      lp.single_apply_ne _ _ _ hmn, norm_zero]
    exact hε⟩
  map_zero' := by
    apply Subtype.ext
    refine lp.ext (funext fun m ↦ ?_)
    by_cases hm : m = n
    · subst m
      simp
    · simp
  map_add' x y := by
    apply Subtype.ext
    refine lp.ext (funext fun m ↦ ?_)
    by_cases hm : m = n
    · subst m
      simp
    · simp [hm]
  map_mul' x y := by
    apply Subtype.ext
    refine lp.ext (funext fun m ↦ ?_)
    by_cases hm : m = n
    · subst m
      simp
    · simp [hm]
  map_smul' c x := by
    apply Subtype.ext
    refine lp.ext (funext fun m ↦ ?_)
    by_cases hm : m = n
    · subst m
      simp
    · simp [hm]
  map_star' x := by
    apply Subtype.ext
    refine lp.ext (funext fun m ↦ ?_)
    by_cases hm : m = n
    · subst m
      simp [lp.star_apply]
    · simp [lp.star_apply, hm]

@[simp] theorem summandInclusion_apply_self (n : ℕ) (x : D n) :
    ((summandInclusion D n x : C0DirectSum D) :
      BoundedCStarSequence D) n = x :=
  lp.single_apply_self ∞ n x

@[simp] theorem summandInclusion_apply_ne {n m : ℕ} (h : m ≠ n)
    (x : D n) :
    ((summandInclusion D n x : C0DirectSum D) :
      BoundedCStarSequence D) m = 0 :=
  lp.single_apply_ne ∞ n x h

/-- Every coordinate summand is a two-sided ideal in the `c₀`-sum. -/
theorem summandInclusion_isIdeal (n : ℕ) :
    IsIdealHom (summandInclusion D n) := by
  constructor
  · intro b x
    refine ⟨b.1 n * x, ?_⟩
    apply Subtype.ext
    refine lp.ext (funext fun m ↦ ?_)
    by_cases hm : m = n
    · subst m
      simp
    · simp [summandInclusion_apply_ne, hm]
  · intro b x
    refine ⟨x * b.1 n, ?_⟩
    apply Subtype.ext
    refine lp.ext (funext fun m ↦ ?_)
    by_cases hm : m = n
    · subst m
      simp
    · simp [summandInclusion_apply_ne, hm]

/-! ## Finite truncations -/

/-- Keep the first `N` coordinates of a `c₀` sequence. -/
def truncation (b : C0DirectSum D) (N : ℕ) : C0DirectSum D :=
  ∑ n ∈ Finset.range N, summandInclusion D n (b.1 n)

private theorem sum_apply (S : Finset ℕ) (f : ℕ → C0DirectSum D) (m : ℕ) :
    (((∑ n ∈ S, f n : C0DirectSum D) : C0DirectSum D) :
      BoundedCStarSequence D) m =
      ∑ n ∈ S, ((f n : C0DirectSum D) : BoundedCStarSequence D) m := by
  let ev : C0DirectSum D →+ D m :=
    { toFun := fun x ↦ x.1 m
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact map_sum ev (fun n ↦ f n) S

@[simp] theorem truncation_apply (b : C0DirectSum D) (N m : ℕ) :
    ((truncation D b N : C0DirectSum D) : BoundedCStarSequence D) m =
      if m < N then b.1 m else 0 := by
  classical
  by_cases hm : m < N
  · rw [if_pos hm]
    rw [truncation, sum_apply]
    rw [Finset.sum_eq_single m]
    · exact summandInclusion_apply_self D m (b.1 m)
    · intro i hi him
      exact summandInclusion_apply_ne D (Ne.symm him) (b.1 i)
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hm))
  · rw [if_neg hm]
    rw [truncation, sum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have hmi : m ≠ i := by
      intro hmi
      subst i
      exact hm (Finset.mem_range.mp hi)
    exact summandInclusion_apply_ne D hmi (b.1 i)

/-- Finite coordinate truncations converge in the supremum norm to a `c₀`
sequence. -/
theorem tendsto_truncation (b : C0DirectSum D) :
    Tendsto (fun N ↦ truncation D b N) atTop (𝓝 b) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have he2 : 0 < ε / 2 := half_pos hε
  have hbnull : Tendsto (fun n ↦ ‖b.1 n‖) atTop (𝓝 0) := b.2
  rw [Metric.tendsto_atTop] at hbnull
  obtain ⟨N, hN⟩ := hbnull (ε / 2) he2
  refine ⟨N, fun M hNM ↦ ?_⟩
  rw [dist_eq_norm]
  change ‖((truncation D b M).1 - b.1 : BoundedCStarSequence D)‖ < ε
  rw [lp.norm_eq_ciSup]
  apply lt_of_le_of_lt (ciSup_le fun m ↦ ?_) (half_lt_self hε)
  by_cases hm : m < M
  · rw [show ((truncation D b M).1 - b.1) m = 0 by
      simp [truncation_apply, hm]]
    simpa using he2.le
  · have hMm : M ≤ m := Nat.le_of_not_gt hm
    have hNm : N ≤ m := hNM.trans hMm
    have htail := hN m hNm
    rw [Real.dist_eq, sub_zero, abs_norm] at htail
    rw [show ((truncation D b M).1 - b.1) m = -b.1 m by
      simp [truncation_apply, hm]]
    simpa using htail.le

/-- A nonunital star representation is continuous, by automatic
contractivity. -/
private theorem nonUnitalStarAlgHom_continuous
    {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) : Continuous f := by
  exact (LipschitzWith.of_dist_le_mul (K := 1) fun x y ↦ by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub]
    calc
      ‖f (x - y)‖ ≤ ‖x - y‖ :=
        NonUnitalStarAlgHom.norm_apply_le f (x - y)
      _ = dist x y := (dist_eq_norm x y).symm).continuous

/-- The coordinate summands are exhaustive: a representation which vanishes
on every one of them vanishes on the whole `c₀`-sum. -/
theorem summandInclusion_isSummandExhaustive :
    IsSummandExhaustive.{u, v} (summandInclusion D) := by
  intro H _ _ _ π hπ b
  have hzero : ∀ N, π (truncation D b N) = 0 := by
    intro N
    simp [truncation, hπ]
  have hlim : Tendsto (fun N ↦ π (truncation D b N)) atTop (𝓝 (π b)) :=
    (nonUnitalStarAlgHom_continuous π).continuousAt.tendsto.comp
      (tendsto_truncation D b)
  have hlimZero : Tendsto (fun N ↦ π (truncation D b N)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun N ↦ (hzero N).symm)
  exact tendsto_nhds_unique hlim hlimZero

/-- Type I passes to the genuine countable `c₀`-sum. -/
theorem isTypeINonUnital_c0DirectSum
    (hD : ∀ n, IsTypeINonUnital.{u, v} (D n)) :
    IsTypeINonUnital.{u, v} (C0DirectSum D) :=
  isTypeINonUnital_of_summands (summandInclusion D)
    (summandInclusion_isIdeal D) (summandInclusion_isSummandExhaustive D) hD

/-- Consequently the ordinary unitization of the genuine `c₀`-sum is type I. -/
theorem isTypeI_unitization_c0DirectSum
    (hD : ∀ n, IsTypeINonUnital.{u, v} (D n)) :
    IsTypeI.{u, v} (Unitization ℂ (C0DirectSum D)) :=
  isTypeI_unitization (isTypeINonUnital_c0DirectSum D hD)

end

end CStarC0DirectSum
end GroupApproximation
