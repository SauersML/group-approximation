import GroupApproximation.Analysis.GoldbringHartRoute
import GroupApproximation.Analysis.HilbertSchmidtPolarCorrection
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCoronaNormSeparation
import GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.RepresentativeNormLe
import GroupApproximation.Meta.AxiomGuard

/-!
# Lifting across the trace-kernel quotient `𝒬 → ∏_ω M_{k_n}`

Lane `nm-tww-07`.  The canonical ⋆-homomorphism
`normMatrixCStarCoronaToTracialMatrixQuotient X ω hω` from the cofinite norm-matrix corona
onto the tracial matrix quotient along a free ultrafilter has Kaplansky-type lifts.

* `traceKernel_surjective`: it is surjective.
* `exists_lift_norm_le`: every `x` has a lift `y` with `‖y‖ ≤ ‖x‖`, via
  `exists_rep_norm_le` and `‖[a]‖_corona = limsup ‖aₙ‖ ≤ ‖a‖`.
* `exists_selfAdjoint_lift_norm_le`: a self-adjoint `x` has a self-adjoint lift with
  `‖y‖ ≤ ‖x‖`, by averaging a norm-bounded lift with its adjoint.
* `exists_unitary_lift`: a unitary `x` has a unitary lift.  Take any representative `a`,
  and replace each coordinate by the printed Hilbert–Schmidt polar correction `U n` with
  `‖U n − a n‖₂ ≤ ‖(a n)ᴴ (a n) − 1‖₂`.  The right side tends to `0` along `ω` because
  `x⋆x = 1`.
-/

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift

open Filter Matrix TracialUltraproduct
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The corona norm of a class is at most the ℓ∞ norm of the sequence. -/
theorem norm_normMatrixCStarCoronaMk_le (a : ModelBoundedSequence X) :
    ‖normMatrixCStarCoronaMk (fun n ↦ X n) a‖ ≤ ‖a‖ := by
  rw [Manuscript.OneSidedMFRadical.norm_normMatrixCStarCoronaMk_eq_limsup (fun n ↦ X n) a]
  exact Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_le Filter.cofinite fun n ↦ norm_nonneg (a n))
    (Filter.Eventually.of_forall fun n ↦
      boundedMatrixSequence_coord_norm_le (fun n ↦ X n) a n)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.norm_normMatrixCStarCoronaMk_le

/-- **The trace-kernel quotient map is surjective.** -/
theorem traceKernel_surjective (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    Function.Surjective (normMatrixCStarCoronaToTracialMatrixQuotient X ω hω) := by
  intro x
  obtain ⟨a, ha, -⟩ := tracialQuot_exists_rep_norm_lt (X := X) (l := (ω : Filter ℕ)) x one_pos
  exact ⟨normMatrixCStarCoronaMk (fun n ↦ X n) a, by
    rw [normMatrixCStarCoronaToTracialMatrixQuotient_mk, ha]⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.traceKernel_surjective

/-- **Norm-bounded lifting**: every class has a lift of no larger norm. -/
theorem exists_lift_norm_le (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (x : TracialMatrixQuotient X (ω : Filter ℕ)) :
    ∃ y : NormMatrixCStarCorona (fun n ↦ X n), ‖y‖ ≤ ‖x‖ ∧
      normMatrixCStarCoronaToTracialMatrixQuotient X ω hω y = x := by
  obtain ⟨c, hc, hcn⟩ := exists_rep_norm_le ω hω x
  exact ⟨normMatrixCStarCoronaMk (fun n ↦ X n) c, (norm_normMatrixCStarCoronaMk_le c).trans hcn,
    by rw [normMatrixCStarCoronaToTracialMatrixQuotient_mk, hc]⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.exists_lift_norm_le

/-- **Self-adjoint norm-bounded lifting.** -/
theorem exists_selfAdjoint_lift_norm_le (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite) (x : TracialMatrixQuotient X (ω : Filter ℕ))
    (hx : IsSelfAdjoint x) :
    ∃ y : NormMatrixCStarCorona (fun n ↦ X n), IsSelfAdjoint y ∧ ‖y‖ ≤ ‖x‖ ∧
      normMatrixCStarCoronaToTracialMatrixQuotient X ω hω y = x := by
  obtain ⟨y0, hy0, hπ⟩ := exists_lift_norm_le ω hω x
  have h2 : IsSelfAdjoint (2⁻¹ : ℂ) := by
    show star (2⁻¹ : ℂ) = 2⁻¹
    rw [star_inv₀, star_ofNat]
  refine ⟨(2⁻¹ : ℂ) • (y0 + star y0), IsSelfAdjoint.smul h2 (IsSelfAdjoint.add_star_self y0),
    ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_ofNat]
    calc (2 : ℝ)⁻¹ * ‖y0 + star y0‖ ≤ (2 : ℝ)⁻¹ * (‖y0‖ + ‖star y0‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ = ‖y0‖ := by
          rw [norm_star]
          ring
      _ ≤ ‖x‖ := hy0
  · rw [map_smul, map_add, map_star, hπ, hx.star_eq, ← two_smul ℂ x, smul_smul,
      inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.exists_selfAdjoint_lift_norm_le

/-- **Unitary lifting**: every unitary of the tracial quotient lifts to a unitary of the
norm-matrix corona. -/
theorem exists_unitary_lift (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (x : TracialMatrixQuotient X (ω : Filter ℕ))
    (hx : x ∈ unitary (TracialMatrixQuotient X (ω : Filter ℕ))) :
    ∃ y ∈ unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      normMatrixCStarCoronaToTracialMatrixQuotient X ω hω y = x := by
  obtain ⟨a, ha, -⟩ := tracialQuot_exists_rep_norm_lt (X := X) (l := (ω : Filter ℕ)) x one_pos
  choose U hU hUd using fun n ↦ HilbertSchmidtPolar.exists_unitary_hsNorm_sub_le (X n) (a n)
  have hU1 : ∀ n, ‖U n‖ ≤ 1 := fun n ↦ le_of_eq (CStarRing.norm_of_mem_unitary (hU n))
  let u : ModelBoundedSequence X := ShulmanTrace.boundedSeqOfBound U hU1
  have hsu : star u * u = 1 := by
    apply lp.ext
    funext n
    rw [ShulmanTrace.modelSeq_mul_apply, ShulmanTrace.modelSeq_star_apply,
      ShulmanTrace.modelSeq_one_apply]
    exact Matrix.mem_unitaryGroup_iff'.mp (hU n)
  have hus : u * star u = 1 := by
    apply lp.ext
    funext n
    rw [ShulmanTrace.modelSeq_mul_apply, ShulmanTrace.modelSeq_star_apply,
      ShulmanTrace.modelSeq_one_apply]
    exact Matrix.mem_unitaryGroup_iff.mp (hU n)
  have hmku : normMatrixCStarCoronaMk (fun n ↦ X n) u ∈
      unitary (NormMatrixCStarCorona (fun n ↦ X n)) := by
    refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
    · rw [normMatrixCStarCorona_star_mk, ← map_mul, hsu, map_one]
    · rw [normMatrixCStarCorona_star_mk, ← map_mul, hus, map_one]
  have hgram : IsHilbertSchmidtNull X (ω : Filter ℕ) (star a * a - 1) :=
    (tracialMatrixQuotientMk_eq_zero_iff X (ω : Filter ℕ) _).mp (by
      rw [map_sub, map_mul, map_one, ← tracialMatrixQuotient_star_mk, ha,
        Unitary.star_mul_self_of_mem hx, sub_self])
  have hnull : IsHilbertSchmidtNull X (ω : Filter ℕ) (u - a) := by
    show Tendsto (fun n ↦ hsNorm (X n) ((u - a) n)) (ω : Filter ℕ) (nhds 0)
    refine squeeze_zero (fun n ↦ hsNorm_nonneg _ _) (fun n ↦ ?_)
      (show Tendsto (fun n ↦ hsNorm (X n) ((star a * a - 1) n)) (ω : Filter ℕ) (nhds 0) from
        hgram)
    show hsNorm (X n) ((u - a) n) ≤ hsNorm (X n) ((star a * a - 1) n)
    rw [ShulmanTrace.modelSeq_sub_apply, ShulmanTrace.modelSeq_sub_apply,
      ShulmanTrace.modelSeq_mul_apply, ShulmanTrace.modelSeq_star_apply,
      ShulmanTrace.modelSeq_one_apply, Matrix.star_eq_conjTranspose]
    exact hUd n
  refine ⟨normMatrixCStarCoronaMk (fun n ↦ X n) u, hmku, ?_⟩
  rw [normMatrixCStarCoronaToTracialMatrixQuotient_mk,
    ShulmanTrace.mk_eq_mk_of_isHilbertSchmidtNull hnull, ha]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.exists_unitary_lift

end

end GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift
