import GroupApproximation.Analysis.VoiculescuGlimmBound
import GroupApproximation.Analysis.VoiculescuProjectionSequence

/-!
# (V2) From vectors off a subspace to a bound on the state

`Analysis/VoiculescuGlimmBound` bounds a state that kills the compacts by any
compact compression of its argument.  The separation step of Glimm's lemma will
supply its hypothesis in a different currency — a bound on `re ⟪b ξ, ξ⟫` for
vectors `ξ` orthogonal to a prescribed finite-dimensional subspace — and this
module is the exchange between the two.

It is short because the compression *is* the projection: compressing by
`1 - P_V` is exactly restricting attention to `Vᗮ`, so a hypothesis about
vectors there is already a statement about the compression, and the only work
is moving `1 - P_V` across an inner product.

## The one place the sign matters

The natural conclusion is `(1-P) b (1-P) ≤ t • 1`, and that is **false** for
negative `t`: compressing shrinks `‖(1-P)η‖` below `‖η‖`, which reverses
`t ‖(1-P)η‖² ≤ t ‖η‖²` when `t < 0`.  The remedy is not a case split and not a
shift, but a better statement — `≤ t • (1 - P)` — together with
`ρ(1 - P) = 1`, which holds because `P` is compact and `ρ` annihilates the
compacts.  So the bound is taken against an arbitrary `y` with `ρ y = 1` rather
than against `1`, and every sign works with no case analysis.  That the
projection is compact is doing real work there, not bookkeeping.

The quadratic forms are written with the operator in the *left* slot
throughout, matching `ContinuousLinearMap.reApplyInnerSelf`, so that building
the positivity of the difference needs no conjugation step.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The bound against an arbitrary unit.**  `Analysis/VoiculescuGlimmBound`
states this against `1`; the compression argument needs it against `1 - P`,
whose `ρ`-value is also `1`. -/
theorem re_apply_le_of_le_smul (ρ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hpos : ∀ T : H →L[ℂ] H, 0 ≤ T → ∃ r : ℝ, 0 ≤ r ∧ ρ T = r)
    {y : H →L[ℂ] H} (hy : ρ y = 1) {x : H →L[ℂ] H} {t : ℝ}
    (hx : x ≤ (t : ℂ) • y) : (ρ x).re ≤ t := by
  have hsub : (0 : H →L[ℂ] H) ≤ (t : ℂ) • y - x :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hx
  obtain ⟨r, hr0, hr⟩ := hpos _ hsub
  have hlin : ρ ((t : ℂ) • y - x) = (t : ℂ) - ρ x := by
    rw [map_sub, map_smul, smul_eq_mul, hy, mul_one]
  rw [hlin] at hr
  have hre := congrArg Complex.re hr
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  linarith

omit [CompleteSpace H] in
/-- A functional that is `1` at `1` and kills the compacts is `1` at `1 - e`
for every compact `e`.  This is what makes the sign-free bound available. -/
theorem apply_one_sub_eq_one (ρ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (hone : ρ 1 = 1)
    (hK : ∀ T : H →L[ℂ] H, IsCompactOperator T → ρ T = 0)
    {e : H →L[ℂ] H} (he : IsCompactOperator e) : ρ (1 - e) = 1 := by
  rw [map_sub, hone, hK e he, sub_zero]

/-- **The exchange.**  A bound on `b` over vectors orthogonal to `V` is a bound
on the compression of `b` by `1 - P_V`, in the shape the state bound consumes. -/
theorem compress_le_smul_of_inner_le (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    {b : H →L[ℂ] H} (hsa : IsSelfAdjoint b) {t : ℝ}
    (hb : ∀ ξ : H, ξ ∈ Vᗮ → RCLike.re ⟪b ξ, ξ⟫_ℂ ≤ t * ‖ξ‖ ^ 2) :
    (1 - V.starProjection) * b * (1 - V.starProjection)
      ≤ (t : ℂ) • (1 - V.starProjection) := by
  have hQsa : IsSelfAdjoint (1 - V.starProjection : H →L[ℂ] H) :=
    IsSelfAdjoint.sub (IsSelfAdjoint.one _) (isSelfAdjoint_starProjection V)
  have hQidem : (1 - V.starProjection : H →L[ℂ] H) * (1 - V.starProjection)
      = 1 - V.starProjection := by
    have hP : (V.starProjection : H →L[ℂ] H) * V.starProjection = V.starProjection :=
      V.isIdempotentElem_starProjection
    rw [sub_mul, one_mul, mul_sub, mul_one, hP, sub_self, sub_zero]
  have hSsa : IsSelfAdjoint ((t : ℂ) • (1 : H →L[ℂ] H) - b) := by
    have hts : star ((t : ℂ) • (1 : H →L[ℂ] H)) = (t : ℂ) • (1 : H →L[ℂ] H) := by
      rw [star_smul, Complex.star_def, Complex.conj_ofReal, star_one]
    show star _ = _
    rw [star_sub, hts, hsa.star_eq]
  have hfactor : (t : ℂ) • (1 - V.starProjection)
      - (1 - V.starProjection) * b * (1 - V.starProjection)
      = (1 - V.starProjection) * ((t : ℂ) • (1 : H →L[ℂ] H) - b)
        * (1 - V.starProjection) := by
    have hone : (1 - V.starProjection : H →L[ℂ] H) * ((t : ℂ) • (1 : H →L[ℂ] H))
        * (1 - V.starProjection) = (t : ℂ) • (1 - V.starProjection) := by
      rw [mul_smul_comm, mul_one, smul_mul_assoc, hQidem]
    calc (t : ℂ) • (1 - V.starProjection)
          - (1 - V.starProjection) * b * (1 - V.starProjection)
        = (1 - V.starProjection) * ((t : ℂ) • (1 : H →L[ℂ] H))
            * (1 - V.starProjection)
          - (1 - V.starProjection) * b * (1 - V.starProjection) := by rw [hone]
      _ = ((1 - V.starProjection) * ((t : ℂ) • (1 : H →L[ℂ] H))
            - (1 - V.starProjection) * b) * (1 - V.starProjection) :=
          (sub_mul _ _ _).symm
      _ = (1 - V.starProjection) * ((t : ℂ) • (1 : H →L[ℂ] H) - b)
            * (1 - V.starProjection) :=
          congrArg (fun z : H →L[ℂ] H ↦ z * (1 - V.starProjection))
            (mul_sub _ _ _).symm
  have hadj : ContinuousLinearMap.adjoint (1 - V.starProjection : H →L[ℂ] H)
      = 1 - V.starProjection := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hQsa.star_eq
  refine ContinuousLinearMap.isPositive_def'.mpr ?_
  rw [hfactor]
  refine ⟨hSsa.conjugate_self hQsa, fun η ↦ ?_⟩
  have hmem : (1 - V.starProjection : H →L[ℂ] H) η ∈ Vᗮ :=
    V.sub_starProjection_mem_orthogonal η
  have hmove : ⟪((1 - V.starProjection) * ((t : ℂ) • (1 : H →L[ℂ] H) - b)
        * (1 - V.starProjection)) η, η⟫_ℂ
      = ⟪((t : ℂ) • (1 : H →L[ℂ] H) - b) ((1 - V.starProjection) η),
          (1 - V.starProjection) η⟫_ℂ := by
    have hkey := ContinuousLinearMap.adjoint_inner_left
      (1 - V.starProjection : H →L[ℂ] H) η
      (((t : ℂ) • (1 : H →L[ℂ] H) - b) ((1 - V.starProjection) η))
    rw [hadj] at hkey
    exact hkey
  have hsplit : ⟪((t : ℂ) • (1 : H →L[ℂ] H) - b) ((1 - V.starProjection) η),
        (1 - V.starProjection) η⟫_ℂ
      = (t : ℂ) * ⟪(1 - V.starProjection) η, (1 - V.starProjection) η⟫_ℂ
        - ⟪b ((1 - V.starProjection) η), (1 - V.starProjection) η⟫_ℂ := by
    have hone_apply : (1 : H →L[ℂ] H) ((1 - V.starProjection) η)
        = (1 - V.starProjection) η := rfl
    rw [sub_apply, inner_sub_left, smul_apply, hone_apply, inner_smul_left,
      Complex.conj_ofReal]
  have hself : RCLike.re ((t : ℂ) * ⟪(1 - V.starProjection) η,
      (1 - V.starProjection) η⟫_ℂ) = t * ‖(1 - V.starProjection) η‖ ^ 2 := by
    have h2 : ⟪(1 - V.starProjection) η, (1 - V.starProjection) η⟫_ℂ
        = ((‖(1 - V.starProjection) η‖ : ℝ) : ℂ) ^ 2 :=
      inner_self_eq_norm_sq_to_K _
    rw [h2, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  show 0 ≤ RCLike.re ⟪_, _⟫_ℂ
  rw [hmove, hsplit, map_sub, hself]
  have := hb _ hmem
  linarith

/-- **The connector.**  A bound over unit vectors orthogonal to a
finite-dimensional subspace bounds the state.  This is the form the separation
step of Glimm's lemma consumes. -/
theorem re_apply_le_of_inner_le (ρ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hpos : ∀ T : H →L[ℂ] H, 0 ≤ T → ∃ r : ℝ, 0 ≤ r ∧ ρ T = r)
    (hone : ρ 1 = 1) (hK : ∀ T : H →L[ℂ] H, IsCompactOperator T → ρ T = 0)
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] {b : H →L[ℂ] H}
    (hsa : IsSelfAdjoint b) {t : ℝ}
    (hb : ∀ ξ : H, ξ ∈ Vᗮ → RCLike.re ⟪b ξ, ξ⟫_ℂ ≤ t * ‖ξ‖ ^ 2) :
    (ρ b).re ≤ t := by
  have hPcpt : IsCompactOperator (V.starProjection : H →L[ℂ] H) :=
    isCompactOperator_starProjection V
  have hy : ρ (1 - V.starProjection) = 1 := apply_one_sub_eq_one ρ hone hK hPcpt
  have hle := re_apply_le_of_le_smul ρ hpos hy
    (compress_le_smul_of_inner_le V hsa hb)
  have hcomp : ρ ((1 - V.starProjection) * b * (1 - V.starProjection)) = ρ b :=
    apply_compress_eq_of_annihilates_compacts ρ hK _ b hPcpt
  rwa [hcomp] at hle

end

end ShulmanFill
end GroupApproximation
