import GroupApproximation.Analysis.VoiculescuOneStep

/-!
# (V4) From the compression defect to the intertwining defect

The one-step approximation of `Analysis/VoiculescuOneStep` controls
`V⋆σ(a)V - ρ(a)`.  The assembly above it needs `σ(a)V - Vρ(a)`, because it is the
intertwining defect that becomes compact in the limit, and this module is the
exchange between the two.

## The identity

With `A = V⋆σ(a⋆a)V - ρ(a⋆a)`, `B = V⋆σ(a⋆)V - ρ(a⋆)` and
`C = V⋆σ(a)V - ρ(a)`, and with `X = σ(a)V - Vρ(a)`,

    `X⋆X = A - Bρ(a) - ρ(a⋆)C` ,

exactly — every other term cancels, using only `V⋆V = 1` and that `σ` and `ρ` are
`⋆`-homomorphisms.  So the C⋆-identity turns three compression bounds into one
intertwining bound, at the cost of a square root: `‖X‖² ≤ d(1 + 2‖ρ(a)‖)`.

This is why the finite set the one-step approximation is run on has to be closed
under `a ↦ a⋆` and `a ↦ a⋆a`: three compressions are needed, not one.  The bound
degrades to a square root, which is why the assembly runs the approximation at
`ε²` rather than `ε`.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

variable {H K₀ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀]
  [CompleteSpace K₀]

/-- **The exact identity.**  The Gram operator of the intertwining defect is a
combination of three compression defects. -/
theorem adjoint_intertwine_comp_self (V : K₀ →L[ℂ] H)
    (hV : ContinuousLinearMap.adjoint V ∘L V = 1)
    (sa sb sc : H →L[ℂ] H) (ra rb rc : K₀ →L[ℂ] K₀)
    (hsa : ContinuousLinearMap.adjoint sa = sb) (hsc : sb ∘L sa = sc)
    (hra : ContinuousLinearMap.adjoint ra = rb) (hrc : rb ∘L ra = rc) :
    ContinuousLinearMap.adjoint (sa ∘L V - V ∘L ra) ∘L (sa ∘L V - V ∘L ra)
      = (ContinuousLinearMap.adjoint V ∘L sc ∘L V - rc)
        - ((ContinuousLinearMap.adjoint V ∘L sb ∘L V - rb) ∘L ra)
        - (rb ∘L (ContinuousLinearMap.adjoint V ∘L sa ∘L V - ra)) := by
  have hXadj : ContinuousLinearMap.adjoint (sa ∘L V - V ∘L ra)
      = (ContinuousLinearMap.adjoint V ∘L sb)
        - (rb ∘L ContinuousLinearMap.adjoint V) := by
    rw [map_sub, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      hsa, hra]
  have hVx : ∀ y : K₀, ContinuousLinearMap.adjoint V (V y) = y := by
    intro y
    have h := congrArg (fun T : K₀ →L[ℂ] K₀ ↦ T y) hV
    simpa using h
  have hscx : ∀ y : H, sb (sa y) = sc y := by
    intro y
    have h := congrArg (fun T : H →L[ℂ] H ↦ T y) hsc
    simpa using h
  have hrcx : ∀ y : K₀, rb (ra y) = rc y := by
    intro y
    have h := congrArg (fun T : K₀ →L[ℂ] K₀ ↦ T y) hrc
    simpa using h
  rw [hXadj]
  ext x
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    sub_apply, map_sub, hVx, hscx, hrcx]
  abel

/-- **The exchange.**  Three compression bounds give one intertwining bound. -/
theorem norm_intertwine_sq_le (V : K₀ →L[ℂ] H)
    (hV : ContinuousLinearMap.adjoint V ∘L V = 1)
    (sa sb sc : H →L[ℂ] H) (ra rb rc : K₀ →L[ℂ] K₀)
    (hsa : ContinuousLinearMap.adjoint sa = sb) (hsc : sb ∘L sa = sc)
    (hra : ContinuousLinearMap.adjoint ra = rb) (hrc : rb ∘L ra = rc)
    {d : ℝ}
    (h1 : ‖ContinuousLinearMap.adjoint V ∘L sc ∘L V - rc‖ ≤ d)
    (h2 : ‖ContinuousLinearMap.adjoint V ∘L sb ∘L V - rb‖ ≤ d)
    (h3 : ‖ContinuousLinearMap.adjoint V ∘L sa ∘L V - ra‖ ≤ d) :
    ‖sa ∘L V - V ∘L ra‖ ^ 2 ≤ d * (1 + ‖ra‖ + ‖rb‖) := by
  have hd0 : 0 ≤ d := le_trans (norm_nonneg _) h1
  have hsq : ‖sa ∘L V - V ∘L ra‖ ^ 2
      = ‖ContinuousLinearMap.adjoint (sa ∘L V - V ∘L ra) ∘L (sa ∘L V - V ∘L ra)‖ := by
    rw [ContinuousLinearMap.norm_adjoint_comp_self, sq]
  rw [hsq, adjoint_intertwine_comp_self V hV sa sb sc ra rb rc hsa hsc hra hrc]
  have hb1 : ‖(ContinuousLinearMap.adjoint V ∘L sb ∘L V - rb) ∘L ra‖
      ≤ d * ‖ra‖ :=
    ((ContinuousLinearMap.adjoint V ∘L sb ∘L V - rb).opNorm_comp_le ra).trans
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  have hb2 : ‖rb ∘L (ContinuousLinearMap.adjoint V ∘L sa ∘L V - ra)‖
      ≤ ‖rb‖ * d :=
    (rb.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
  calc ‖(ContinuousLinearMap.adjoint V ∘L sc ∘L V - rc)
          - ((ContinuousLinearMap.adjoint V ∘L sb ∘L V - rb) ∘L ra)
          - (rb ∘L (ContinuousLinearMap.adjoint V ∘L sa ∘L V - ra))‖
      ≤ ‖(ContinuousLinearMap.adjoint V ∘L sc ∘L V - rc)
          - ((ContinuousLinearMap.adjoint V ∘L sb ∘L V - rb) ∘L ra)‖
        + ‖rb ∘L (ContinuousLinearMap.adjoint V ∘L sa ∘L V - ra)‖ := norm_sub_le _ _
    _ ≤ (‖ContinuousLinearMap.adjoint V ∘L sc ∘L V - rc‖
          + ‖(ContinuousLinearMap.adjoint V ∘L sb ∘L V - rb) ∘L ra‖)
        + ‖rb ∘L (ContinuousLinearMap.adjoint V ∘L sa ∘L V - ra)‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (d + d * ‖ra‖) + ‖rb‖ * d := add_le_add (add_le_add h1 hb1) hb2
    _ = d * (1 + ‖ra‖ + ‖rb‖) := by ring

/-- **The exchange, at a star subalgebra of `B(H)`.**  The three compressions are
the ones at `a`, `a⋆` and `a⋆a`, which is why the finite set the one-step
approximation runs on has to be closed under those two operations. -/
theorem norm_intertwine_sq_le_of_compress {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀)) (V : K₀ →L[ℂ] H)
    (hV : ContinuousLinearMap.adjoint V ∘L V = 1) (a : ↥A) {d : ℝ}
    (h1 : ‖ContinuousLinearMap.adjoint V ∘L ((star a * a : ↥A) : H →L[ℂ] H) ∘L V
      - rho (star a * a)‖ ≤ d)
    (h2 : ‖ContinuousLinearMap.adjoint V ∘L ((star a : ↥A) : H →L[ℂ] H) ∘L V
      - rho (star a)‖ ≤ d)
    (h3 : ‖ContinuousLinearMap.adjoint V ∘L (a : H →L[ℂ] H) ∘L V - rho a‖ ≤ d) :
    ‖(a : H →L[ℂ] H) ∘L V - V ∘L rho a‖ ^ 2 ≤ d * (1 + 2 * ‖rho a‖) := by
  have hsa : ContinuousLinearMap.adjoint (a : H →L[ℂ] H)
      = ((star a : ↥A) : H →L[ℂ] H) := by
    rw [StarMemClass.coe_star, ← ContinuousLinearMap.star_eq_adjoint]
  have hsc : ((star a : ↥A) : H →L[ℂ] H) ∘L (a : H →L[ℂ] H)
      = ((star a * a : ↥A) : H →L[ℂ] H) := rfl
  have hra : ContinuousLinearMap.adjoint (rho a) = rho (star a) := by
    rw [map_star, ← ContinuousLinearMap.star_eq_adjoint]
  have hrc : rho (star a) ∘L rho a = rho (star a * a) := by
    rw [map_mul]
    rfl
  have hnorm : ‖rho (star a)‖ = ‖rho a‖ := by
    rw [map_star, norm_star]
  have h := norm_intertwine_sq_le V hV (a : H →L[ℂ] H) ((star a : ↥A) : H →L[ℂ] H)
    ((star a * a : ↥A) : H →L[ℂ] H) (rho a) (rho (star a)) (rho (star a * a))
    hsa hsc hra hrc h1 h2 h3
  rw [hnorm] at h
  calc ‖(a : H →L[ℂ] H) ∘L V - V ∘L rho a‖ ^ 2
      ≤ d * (1 + ‖rho a‖ + ‖rho a‖) := h
    _ = d * (1 + 2 * ‖rho a‖) := by ring

end

end ShulmanFill
end GroupApproximation
