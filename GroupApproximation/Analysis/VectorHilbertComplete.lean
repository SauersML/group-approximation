import GroupApproximation.Analysis.VectorHilbertUltraproduct
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# `H_ω` is complete, hence a Hilbert space

`Analysis/VectorHilbertUltraproduct.lean` builds the manuscript's `H_ω` -- the
ultraproduct of the coordinate spaces `ℂ^{d_n}` that `\label{thm:normal-kazhdan}`
names -- and gives it its inner product, positive definiteness included.  This
file supplies completeness, so that the printed

> let `H_ω` be the Hilbert-space ultraproduct of the coordinate spaces `ℂ^{d_n}`

names a Hilbert space in mathlib's sense: `InnerProductSpace ℂ` from the
construction, `CompleteSpace` from `vecOmegaCompleteSpace` below.

## The route

The same as for `K_ω` in `Analysis/OmegaHilbertComplete.lean`, and shorter for
the two reasons the construction was shorter.

* `NormedAddCommGroup.completeSpace_of_summable_imp_tendsto` reduces completeness
  to the convergence of absolutely convergent series.
* `exists_rep_vecMass_le` truncates a representative so that it obeys
  `vecMass ξ_n ≤ ‖x‖² + ε` at **every** stage, not merely on a set of `ω`.
  Because the printed vector spaces carry no weight, this needs no clipped
  weight and no `w n = 0` branch.
* The coordinate series then converges in `EuclideanSpace ℂ (Y n)`, which is the
  coordinate space itself rather than a vectorization of it, so the majorant is
  the summable sequence `‖u k‖ + 2^{-k}` with no stage-dependent factor.
-/

namespace GroupApproximation
namespace VectorHilbertComplete

open Filter Topology
open MarkedCompressionVectorChain UltrafilterLimit VectorHilbertUltraproduct

noncomputable section

/-! ## Coordinate helpers -/

section Coordinates

variable {Z : FiniteModel}

theorem vecMass_zero : vecMass (0 : Z → ℂ) = 0 := by
  unfold vecMass
  simp

@[simp] theorem evec_ofLp (v : EuclideanSpace ℂ Z) : evec (WithLp.ofLp v) = v := rfl

theorem vecMass_ofLp (v : EuclideanSpace ℂ Z) :
    vecMass (WithLp.ofLp v) = ‖v‖ ^ 2 := by
  rw [vecMass_eq_norm_sq, evec_ofLp]

theorem vecMass_ofLp_le (v : EuclideanSpace ℂ Z) {R : ℝ} (h : ‖v‖ ≤ R) :
    vecMass (WithLp.ofLp v) ≤ R ^ 2 := by
  rw [vecMass_ofLp]
  nlinarith [h, norm_nonneg v]

theorem ofLp_sum_evec {ι : Type*} (s : Finset ι) (f : ι → Z → ℂ) :
    WithLp.ofLp (∑ i ∈ s, evec (f i)) = ∑ i ∈ s, f i :=
  congrArg WithLp.ofLp (evec_sum s f).symm

end Coordinates

/-! ## Classes, their norms, and normalized representatives -/

section Representatives

variable (Y : ℕ → FiniteModel) (ω : Ultrafilter ℕ)

@[simp] theorem mkV_zero : mkV Y ω 0 = 0 := rfl

@[simp] theorem mkV_add (ξ η : vecBounded Y) :
    mkV Y ω (ξ + η) = mkV Y ω ξ + mkV Y ω η := rfl

theorem mkV_sum (s : Finset ℕ) (f : ℕ → vecBounded Y) :
    mkV Y ω (∑ k ∈ s, f k) = ∑ k ∈ s, mkV Y ω (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, mkV_zero]
  | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, mkV_add, ih]

theorem norm_mkV_sq (ξ : vecBounded Y) :
    ‖mkV Y ω ξ‖ ^ 2 = ulim ω (fun n ↦ vecMass ((ξ : VecFam Y) n)) := by
  rw [norm_mkV]
  exact Real.sq_sqrt
    (ulim_nonneg (exists_tendsto_vecMass ξ) fun n ↦ vecMass_nonneg _)

/-- **A pointwise mass bound bounds the norm of the class.**  With no weight in
the construction this is immediate from `ulim_le`. -/
theorem norm_mkV_le {ζ : vecBounded Y} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ n, vecMass ((ζ : VecFam Y) n) ≤ R ^ 2) : ‖mkV Y ω ζ‖ ≤ R := by
  have hle : ulim ω (fun n ↦ vecMass ((ζ : VecFam Y) n)) ≤ R ^ 2 :=
    ulim_le (exists_tendsto_vecMass ζ) (Eventually.of_forall h)
  calc ‖mkV Y ω ζ‖
      = Real.sqrt (ulim ω (fun n ↦ vecMass ((ζ : VecFam Y) n))) := norm_mkV Y ω ζ
    _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hle
    _ = R := Real.sqrt_sq hR

/-- **Truncation at the norm.**  Every class of `H_ω` has a representative whose
coordinate masses obey `vecMass ξ_n ≤ ‖x‖² + ε` at *every* stage.

An arbitrary representative obeys the bound only on a set of `ω` -- that is what
`lim_ω vecMass ξ_n = ‖x‖²` says -- and setting it to zero off that set changes it
by a family null along `ω`, which is exactly an element of the denominator. -/
theorem exists_rep_vecMass_le (x : VecOmega Y ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : vecBounded Y, mkV Y ω ξ = x ∧
      ∀ n, vecMass ((ξ : VecFam Y) n) ≤ ‖x‖ ^ 2 + ε := by
  classical
  obtain ⟨ξ₀, rfl⟩ := mkV_surjective Y ω x
  have hnn : (0 : ℝ) ≤ ‖mkV Y ω ξ₀‖ ^ 2 + ε := add_nonneg (sq_nonneg _) hε.le
  have hgood : ∀ᶠ n in (ω : Filter ℕ),
      vecMass ((ξ₀ : VecFam Y) n) ≤ ‖mkV Y ω ξ₀‖ ^ 2 + ε := by
    have hlt : ∀ᶠ n in (ω : Filter ℕ),
        vecMass ((ξ₀ : VecFam Y) n) < ‖mkV Y ω ξ₀‖ ^ 2 + ε := by
      refine eventually_lt_of_ulim_lt (exists_tendsto_vecMass ξ₀) ?_
      rw [norm_mkV_sq]
      linarith
    filter_upwards [hlt] with n hn
    exact hn.le
  have hcut : ∀ n, vecMass (if vecMass ((ξ₀ : VecFam Y) n)
        ≤ ‖mkV Y ω ξ₀‖ ^ 2 + ε then (ξ₀ : VecFam Y) n else 0)
      ≤ ‖mkV Y ω ξ₀‖ ^ 2 + ε := by
    intro n
    by_cases hn : vecMass ((ξ₀ : VecFam Y) n) ≤ ‖mkV Y ω ξ₀‖ ^ 2 + ε
    · rw [if_pos hn]
      exact hn
    · rw [if_neg hn, vecMass_zero]
      exact hnn
  refine ⟨⟨fun n ↦ if vecMass ((ξ₀ : VecFam Y) n) ≤ ‖mkV Y ω ξ₀‖ ^ 2 + ε
      then (ξ₀ : VecFam Y) n else 0,
    ⟨‖mkV Y ω ξ₀‖ ^ 2 + ε, hcut⟩⟩, ?_, hcut⟩
  refine (Submodule.Quotient.eq (vecNullIn Y ω)).mpr ?_
  intro δ hδ
  filter_upwards [hgood] with n hn
  show vecMass ((if vecMass ((ξ₀ : VecFam Y) n) ≤ ‖mkV Y ω ξ₀‖ ^ 2 + ε
      then (ξ₀ : VecFam Y) n else 0) - (ξ₀ : VecFam Y) n) ≤ δ
  rw [if_pos hn, sub_self, vecMass_zero]
  exact hδ.le

end Representatives

/-! ## Completeness -/

section Complete

variable {Y : ℕ → FiniteModel} {ω : Ultrafilter ℕ}

/-- **The absolutely convergent series criterion, verified for `H_ω`.** -/
theorem exists_tendsto_sum_of_summable_norm (u : ℕ → VecOmega Y ω)
    (hu : Summable fun k ↦ ‖u k‖) :
    ∃ a, Tendsto (fun N ↦ ∑ k ∈ Finset.range N, u k) atTop (𝓝 a) := by
  classical
  have hbnn : ∀ k : ℕ, (0 : ℝ) ≤ ‖u k‖ + (1 / 2 : ℝ) ^ k := fun k ↦ by positivity
  have hbsum : Summable fun k ↦ ‖u k‖ + (1 / 2 : ℝ) ^ k :=
    hu.add summable_geometric_two
  -- normalized representatives
  have hrep : ∀ k : ℕ, ∃ ξ : vecBounded Y, mkV Y ω ξ = u k ∧
      ∀ n, vecMass ((ξ : VecFam Y) n) ≤ (‖u k‖ + (1 / 2 : ℝ) ^ k) ^ 2 := by
    intro k
    obtain ⟨ξ, hξ1, hξ2⟩ :=
      exists_rep_vecMass_le Y ω (u k) (ε := ((1 / 2 : ℝ) ^ k) ^ 2) (by positivity)
    refine ⟨ξ, hξ1, fun n ↦ (hξ2 n).trans ?_⟩
    nlinarith [norm_nonneg (u k), pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
  choose ξ hξeq hξle using hrep
  -- coordinate norms, with a majorant independent of the stage
  have hnormle : ∀ k n : ℕ, ‖evec ((ξ k : VecFam Y) n)‖
      ≤ ‖u k‖ + (1 / 2 : ℝ) ^ k := by
    intro k n
    rw [norm_evec]
    calc Real.sqrt (vecMass ((ξ k : VecFam Y) n))
        ≤ Real.sqrt ((‖u k‖ + (1 / 2 : ℝ) ^ k) ^ 2) :=
          Real.sqrt_le_sqrt (hξle k n)
      _ = ‖u k‖ + (1 / 2 : ℝ) ^ k := Real.sqrt_sq (hbnn k)
  have hsummable : ∀ n : ℕ, Summable fun k ↦ evec ((ξ k : VecFam Y) n) :=
    fun n ↦ Summable.of_norm_bounded hbsum fun k ↦ hnormle k n
  -- the tail majorants
  have htail : ∀ N : ℕ, Summable fun i ↦ ‖u (i + N)‖ + (1 / 2 : ℝ) ^ (i + N) :=
    fun N ↦ (summable_nat_add_iff N).2 hbsum
  have htailnn : ∀ N : ℕ,
      (0 : ℝ) ≤ ∑' i, (‖u (i + N)‖ + (1 / 2 : ℝ) ^ (i + N)) :=
    fun N ↦ tsum_nonneg fun i ↦ hbnn (i + N)
  have htailbound : ∀ N n : ℕ,
      ‖∑' i, evec ((ξ (i + N) : VecFam Y) n)‖
        ≤ ∑' i, (‖u (i + N)‖ + (1 / 2 : ℝ) ^ (i + N)) :=
    fun N n ↦ tsum_of_norm_bounded (htail N).hasSum fun i ↦ hnormle (i + N) n
  have htailmem : ∀ N : ℕ,
      (fun n ↦ WithLp.ofLp (∑' i, evec ((ξ (i + N) : VecFam Y) n)))
        ∈ vecBounded Y := fun N ↦
    ⟨(∑' i, (‖u (i + N)‖ + (1 / 2 : ℝ) ^ (i + N))) ^ 2, fun n ↦
      vecMass_ofLp_le _ (htailbound N n)⟩
  refine ⟨mkV Y ω ⟨_, htailmem 0⟩, ?_⟩
  have hsplit : ∀ N : ℕ,
      (⟨_, htailmem 0⟩ : vecBounded Y)
        = (∑ k ∈ Finset.range N, ξ k) + ⟨_, htailmem N⟩ := by
    intro N
    have hfam : ∀ n : ℕ,
        WithLp.ofLp (∑' i, evec ((ξ i : VecFam Y) n))
          = (∑ k ∈ Finset.range N, (ξ k : VecFam Y) n)
            + WithLp.ofLp (∑' i, evec ((ξ (i + N) : VecFam Y) n)) := by
      intro n
      rw [← (hsummable n).sum_add_tsum_nat_add N, WithLp.ofLp_add, ofLp_sum_evec]
    refine Subtype.ext (funext fun n ↦ ?_)
    rw [Submodule.coe_add, Pi.add_apply,
      AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    exact hfam n
  have hdiff : ∀ N : ℕ,
      ‖(∑ k ∈ Finset.range N, u k) - mkV Y ω ⟨_, htailmem 0⟩‖
        ≤ ∑' i, (‖u (i + N)‖ + (1 / 2 : ℝ) ^ (i + N)) := by
    intro N
    have hsum : (∑ k ∈ Finset.range N, u k)
        = mkV Y ω (∑ k ∈ Finset.range N, ξ k) := by
      rw [mkV_sum Y ω (Finset.range N) ξ]
      simp only [hξeq]
    have hval : (∑ k ∈ Finset.range N, u k) - mkV Y ω ⟨_, htailmem 0⟩
        = -mkV Y ω ⟨_, htailmem N⟩ := by
      rw [hsum, hsplit N, mkV_add]
      abel
    rw [hval, norm_neg]
    exact norm_mkV_le Y ω (htailnn N) fun n ↦
      vecMass_ofLp_le _ (htailbound N n)
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun N ↦ norm_nonneg _) hdiff ?_
  exact tendsto_sum_nat_add (fun k ↦ ‖u k‖ + (1 / 2 : ℝ) ^ k)

/-- **`H_ω` is complete.**

With `vecOmegaInnerProductSpace` this makes the manuscript's `H_ω` a Hilbert
space, so that the orthogonal complements, orthogonal projections and spectral
theory the printed proof of `thm:normal-kazhdan` uses on it are available. -/
instance vecOmegaCompleteSpace : CompleteSpace (VecOmega Y ω) :=
  NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
    fun u hu ↦ exists_tendsto_sum_of_summable_norm u hu

end Complete

end

end VectorHilbertComplete
end GroupApproximation
