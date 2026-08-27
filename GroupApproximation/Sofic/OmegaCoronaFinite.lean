import GroupApproximation.Sofic.OmegaAlmostRepresentation
import GroupApproximation.Sofic.UltraproductDedekindFinite

/-!
# KT.10 for the printed object: `B_ω` is finite

`Sofic/UltraproductDedekindFinite.lean` proves that the corona is finite --- an
isometry is a unitary --- for the *cofinite* filter, and its own docstring
records the substitution: the printed step is about `B_ω = ∏_ω B(K_n)`.  With
the corona now carrying its filter this file states and proves it for `B_ω`
itself.

## What is shared and what is repeated

Nothing analytic is repeated.  The Neumann-series estimate
`norm_swap_sub_one_le` is about an arbitrary matrix algebra and has no filter in
it; `isNullMatrixSequence_swap` is stated at an arbitrary filter for exactly
this reason; and `KazhdanCornerMatrices.polarCorrectUnitary` is a
finite-dimensional statement about a single matrix.  What is repeated is the
quotient bookkeeping --- surjectivity of the class map, `map_sub`/`map_mul`, and
the null-ideal criterion --- because `B_c` and `B_ω` are different algebras and
a statement about one is not a statement about the other.  That is the whole
point of the row this file closes.

Both routes to finiteness are given, as in the cofinite case: the abstract
one-sided-inverse route (`omegaAdjointCorona_isDedekindFiniteMonoid`) and the
printed polar-correction route (`omega_polar_correction`,
`kt_06_omega_ultraproduct_finite`).  The manuscript argues the second.
-/

namespace GroupApproximation
namespace OmegaCoronaFinite

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (ω : Ultrafilter ℕ)

/-! ## The abstract route -/

/-- **KT.10, abstract form, for `B_ω`.**  A one-sided inverse in `B_ω` is
automatically two-sided.  The estimate behind it is the Neumann series of
`Sofic/UltraproductDedekindFinite.lean`, which has no filter in it. -/
instance omegaAdjointCorona_isDedekindFiniteMonoid :
    IsDedekindFiniteMonoid (OmegaAdjointCorona Y ω) where
  mul_eq_one_symm {x y} hxy := by
    obtain ⟨a, rfl⟩ := omegaMk_surjective Y ω x
    obtain ⟨b, rfl⟩ := omegaMk_surjective Y ω y
    have h0 : omegaMk Y ω (a * b - 1) = 0 := by
      rw [map_sub, map_mul, map_one]
      exact sub_eq_zero.mpr hxy
    have hab : IsNullMatrixSequence (DblIdx Y) (ω : Filter ℕ) (a * b - 1) :=
      (omegaMk_eq_zero_iff Y ω _).mp h0
    have hba : IsNullMatrixSequence (DblIdx Y) (ω : Filter ℕ) (b * a - 1) :=
      isNullMatrixSequence_swap (DblIdx Y) (ω : Filter ℕ) hab
    have h1 : omegaMk Y ω (b * a - 1) = 0 :=
      (omegaMk_eq_zero_iff Y ω _).mpr hba
    rw [map_sub, map_mul, map_one] at h1
    exact sub_eq_zero.mp h1

/-- The isometry form: in `B_ω` every isometry is a unitary. -/
theorem omega_mul_star_eq_one {sigma : OmegaAdjointCorona Y ω}
    (h : star sigma * sigma = 1) : sigma * star sigma = 1 :=
  mul_eq_one_symm h

/-! ## The printed route: polar correction -/

/-- **KT.10 (polar correction) for `B_ω`.**  If `σ*σ = 1` then the coordinate
Gram defects vanish along `ω`, so on a set of `ω` polar correction replaces the
coordinates by genuine unitaries, and the class is unchanged.

This is the manuscript's sentence "polar correction therefore replaces `σ_n` by
a unitary `w_n` with `‖σ_n − w_n‖ → 0`.  Hence `σ = [w_n]_ω`", now at the
`ω` the manuscript writes rather than at the cofinite filter. -/
theorem omega_polar_correction {sigma : OmegaAdjointCorona Y ω}
    (hsigma : star sigma * sigma = 1) :
    ∃ w : ∀ n, Matrix.unitaryGroup (DblFam Y n) ℂ,
      omegaMk Y ω (unitarySequenceBounded (DblFam Y) w) = sigma := by
  obtain ⟨a, rfl⟩ := omegaMk_surjective Y ω sigma
  have hstarmul : omegaMk Y ω (star a) * omegaMk Y ω a = 1 := by
    rw [← OmegaAlmostRepresentation.omegaMk_star]
    exact hsigma
  have hgramZero : omegaMk Y ω (star a * a - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hstarmul, sub_self]
  have hgram : IsNullMatrixSequence (DblIdx Y) (ω : Filter ℕ) (star a * a - 1) :=
    (omegaMk_eq_zero_iff Y ω _).mp hgramZero
  have hgramTendsto : Tendsto (fun n ↦
      ‖KazhdanCornerMatrices.cornerGram
        ((a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n) - 1‖)
      (ω : Filter ℕ) (nhds 0) := by
    simpa [IsNullMatrixSequence, KazhdanCornerMatrices.cornerGram,
      lp.star_apply, Matrix.star_eq_conjTranspose] using hgram
  have hgood : ∀ᶠ n in (ω : Filter ℕ),
      ‖KazhdanCornerMatrices.cornerGram
        ((a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n) - 1‖ ≤ (1 / 2 : ℝ) := by
    have hnear := (Metric.tendsto_nhds.mp hgramTendsto) (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnear] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  let w : ∀ n, Matrix.unitaryGroup (DblFam Y n) ℂ := fun n ↦
    if hn : ‖KazhdanCornerMatrices.cornerGram
        ((a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n) - 1‖ ≤ (1 / 2 : ℝ) then
      KazhdanCornerMatrices.polarCorrectUnitary
        ((a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n)
        (KazhdanCornerMatrices.cornerGram_isHermitian _) hn le_rfl
    else 1
  have hdiff : IsNullMatrixSequence (DblIdx Y) (ω : Filter ℕ)
      (unitarySequenceBounded (DblFam Y) w - a) := by
    apply squeeze_zero'
      (Eventually.of_forall fun n ↦
        norm_nonneg ((unitarySequenceBounded (DblFam Y) w - a) n))
    · filter_upwards [hgood] with n hn
      change ‖(w n : Matrix (DblIdx Y n) (DblIdx Y n) ℂ)
          - (a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖ ≤
        ‖a‖ * (2 * ‖KazhdanCornerMatrices.cornerGram
          ((a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n) - 1‖)
      rw [show w n = KazhdanCornerMatrices.polarCorrectUnitary
          ((a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n)
          (KazhdanCornerMatrices.cornerGram_isHermitian _) hn le_rfl from
        dif_pos hn]
      exact (KazhdanCornerMatrices.norm_polarCorrect_sub_le_mul
        ((a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n)
        (KazhdanCornerMatrices.cornerGram_isHermitian _)
        (norm_nonneg _) hn le_rfl).trans
          (mul_le_mul_of_nonneg_right
            ((lp.isLUB_norm a).1 ⟨n, rfl⟩) (by positivity))
    · simpa only [mul_zero] using
        (hgramTendsto.const_mul 2).const_mul ‖a‖
  refine ⟨w, ?_⟩
  rw [← sub_eq_zero, ← map_sub]
  exact (omegaMk_eq_zero_iff Y ω _).mpr hdiff

/-- **KT.10, as printed.**  `B_ω` is finite: an isometry of the norm
ultraproduct along `ω` is a unitary, proved through polar correction. -/
theorem kt_06_omega_ultraproduct_finite {sigma : OmegaAdjointCorona Y ω}
    (hsigma : star sigma * sigma = 1) : sigma * star sigma = 1 := by
  obtain ⟨w, rfl⟩ := omega_polar_correction Y ω hsigma
  have hww : unitarySequenceBounded (DblFam Y) w
      * star (unitarySequenceBounded (DblFam Y) w) = 1 := by
    ext n i j
    exact congrArg (fun A : Matrix (DblIdx Y n) (DblIdx Y n) ℂ ↦ A i j)
      (Unitary.mul_star_self_of_mem (w n).property)
  have h := congrArg (omegaMk Y ω) hww
  rw [map_mul, map_one] at h
  rw [OmegaAlmostRepresentation.omegaMk_star]
  exact h

/-- The conclusion in the form the transport consumes: an isometry of `B_ω` is
a member of its unitary group. -/
theorem kt_06_omega_mem_unitary {sigma : OmegaAdjointCorona Y ω}
    (hsigma : star sigma * sigma = 1) :
    sigma ∈ unitary (OmegaAdjointCorona Y ω) :=
  ⟨hsigma, kt_06_omega_ultraproduct_finite Y ω hsigma⟩

end

end OmegaCoronaFinite
end GroupApproximation
