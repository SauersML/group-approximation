import GroupApproximation.Analysis.VoiculescuBlockDiagonal

/-!
# (V4) The summation analysis: a blockwise-small operator is compact

This is the analytic step of the assembly.  An operator on a Hilbert sum of
finite-dimensional blocks whose restrictions to the blocks are summable in norm
is compact.  Applied to the defect `σ(a)W - Wρ(a)`, whose restriction to the
`m`-th block is what the intertwining step made smaller than `2⁻ᵐ`, that is
exactly the conclusion (V4) wants.

## Why the tolerances are `ℓ¹` and not `ℓ²`

The obvious route runs `ℓ²`: bound the tail of the decomposition by
Cauchy--Schwarz and show `‖D(1 - Pₙ)‖ → 0`.  Summing in `ℓ¹` instead makes the
whole tail estimate disappear.  The block operators `Bₘ = D ιₘ ιₘ⋆` then have
summable norms, so the series converges *in operator norm* in the Banach space
`K →L[ℂ] H`; its sum is `D`, because evaluating at a vector is continuous and
the blocks resolve the identity; and its partial sums are finite-rank, hence
compact.  Compactness of `D` is then just closedness of the compacts.  Since the
assembly is free to choose its tolerances, `2⁻ᵐ` costs nothing and buys the
simpler argument.

## The one fact Mathlib does not supply

That the `m`-th coordinate of a vector in a Hilbert sum is `ιₘ⋆` applied to it.
`Analysis/InnerProductSpace/l2Space` has the canonical identification and the
`HasSum` for it, but not this identification of the coordinate with an adjoint;
`coord_eq_adjoint_sumBlockIncl` proves it by pairing against `lp.single` on one
side and against the inclusion on the other.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

variable {K H : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {G : ℕ → Type} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)]
  [∀ m, CompleteSpace (G m)]

/-! ## The inclusion of a block, and its adjoint -/

/-- The inclusion of the `m`-th block, as a continuous linear map. -/
def sumBlockIncl (U : ∀ m, G m →ₗᵢ[ℂ] K) (m : ℕ) : G m →L[ℂ] K :=
  (U m).toContinuousLinearMap

omit [CompleteSpace K] [∀ (m : ℕ), CompleteSpace (G m)] in
theorem norm_sumBlockIncl_le (U : ∀ m, G m →ₗᵢ[ℂ] K) (m : ℕ) :
    ‖sumBlockIncl U m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    rw [one_mul]
    exact le_of_eq ((U m).norm_map x)

theorem norm_adjoint_sumBlockIncl_le (U : ∀ m, G m →ₗᵢ[ℂ] K) (m : ℕ) :
    ‖ContinuousLinearMap.adjoint (sumBlockIncl U m)‖ ≤ 1 := by
  rw [LinearIsometryEquiv.norm_map]
  exact norm_sumBlockIncl_le U m

/-! ## The coordinate is the adjoint of the inclusion -/

/-- **The coordinate of a vector in a Hilbert sum is the adjoint of the
inclusion applied to it.**  Mathlib has the canonical identification with
`lp G 2` but not this; it is proved by pairing against `lp.single`. -/
theorem coord_eq_adjoint_sumBlockIncl (U : ∀ m, G m →ₗᵢ[ℂ] K)
    (hU : IsHilbertSum ℂ G U) (x : K) (m : ℕ) :
    (hU.linearIsometryEquiv x) m
      = ContinuousLinearMap.adjoint (sumBlockIncl U m) x := by
  classical
  refine ext_inner_left ℂ fun y ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  have h1 : ⟪(lp.single 2 m y : lp G 2), hU.linearIsometryEquiv x⟫_ℂ
      = ⟪y, (hU.linearIsometryEquiv x) m⟫_ℂ := lp.inner_single_left m y _
  have h2 : ⟪(lp.single 2 m y : lp G 2), hU.linearIsometryEquiv x⟫_ℂ
      = ⟪sumBlockIncl U m y, x⟫_ℂ := by
    have h := hU.linearIsometryEquiv.symm.inner_map_map
      (lp.single 2 m y) (hU.linearIsometryEquiv x)
    rw [hU.linearIsometryEquiv_symm_apply_single,
      LinearIsometryEquiv.symm_apply_apply] at h
    exact h.symm
  rw [← h1, h2]

/-- **The blocks resolve the identity.** -/
theorem hasSum_sumBlockIncl (U : ∀ m, G m →ₗᵢ[ℂ] K) (hU : IsHilbertSum ℂ G U)
    (x : K) :
    HasSum (fun m ↦ sumBlockIncl U m
      (ContinuousLinearMap.adjoint (sumBlockIncl U m) x)) x := by
  have h := hU.hasSum_linearIsometryEquiv_symm (hU.linearIsometryEquiv x)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  have hfun : (fun m ↦ U m ((hU.linearIsometryEquiv x) m))
      = fun m ↦ sumBlockIncl U m
        (ContinuousLinearMap.adjoint (sumBlockIncl U m) x) := by
    funext m
    rw [coord_eq_adjoint_sumBlockIncl U hU x m]
    rfl
  rwa [hfun] at h

/-! ## The compactness -/

/-- **A blockwise-summable operator is compact.**  Its block operators have
summable norms, so the series converges in operator norm; the sum is the
operator, and the partial sums are finite-rank. -/
theorem isCompactOperator_of_summable_blocks [∀ m, FiniteDimensional ℂ (G m)]
    (U : ∀ m, G m →ₗᵢ[ℂ] K) (hU : IsHilbertSum ℂ G U) (D : K →L[ℂ] H)
    (hsum : Summable fun m ↦ ‖D ∘L sumBlockIncl U m‖) : IsCompactOperator D := by
  set B : ℕ → (K →L[ℂ] H) := fun m ↦
    (D ∘L sumBlockIncl U m) ∘L ContinuousLinearMap.adjoint (sumBlockIncl U m)
    with hBdef
  have hnorm : ∀ m, ‖B m‖ ≤ ‖D ∘L sumBlockIncl U m‖ := by
    intro m
    calc ‖B m‖
        ≤ ‖D ∘L sumBlockIncl U m‖
            * ‖ContinuousLinearMap.adjoint (sumBlockIncl U m)‖ :=
          (D ∘L sumBlockIncl U m).opNorm_comp_le _
      _ ≤ ‖D ∘L sumBlockIncl U m‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_adjoint_sumBlockIncl_le U m)
            (norm_nonneg _)
      _ = ‖D ∘L sumBlockIncl U m‖ := mul_one _
  have hBsummable : Summable B := hsum.of_norm_bounded hnorm
  have hSD : (∑' m, B m) = D := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    have h1 : HasSum (fun m ↦ B m x) ((∑' m, B m) x) :=
      hBsummable.hasSum.map (ContinuousLinearMap.apply ℂ H x)
        (ContinuousLinearMap.apply ℂ H x).continuous
    have h2 : HasSum (fun m ↦ B m x) (D x) :=
      (hasSum_sumBlockIncl U hU x).map D D.continuous
    exact h1.unique h2
  have hBcompact : ∀ m, IsCompactOperator (B m) := by
    intro m
    haveI : ProperSpace (G m) := FiniteDimensional.proper ℂ (G m)
    have h1 : IsCompactOperator (D ∘L sumBlockIncl U m) :=
      isCompactOperator_of_locallyCompactSpace_rng _
    have h2 := h1.comp_clm (ContinuousLinearMap.adjoint (sumBlockIncl U m))
    rwa [← ContinuousLinearMap.coe_comp] at h2
  have hpartial : ∀ N : ℕ,
      (∑ m ∈ Finset.range N, B m) ∈ {f : K →L[ℂ] H | IsCompactOperator f} := by
    intro N
    show IsCompactOperator (⇑(∑ m ∈ Finset.range N, B m) : K → H)
    induction N with
    | zero =>
        have h0 : (⇑(∑ m ∈ Finset.range 0, B m) : K → H) = 0 := by simp
        rw [h0]
        exact isCompactOperator_zero
    | succ n ih =>
        have hsucc : (⇑(∑ m ∈ Finset.range (n + 1), B m) : K → H)
            = (⇑(∑ m ∈ Finset.range n, B m) : K → H) + ⇑(B n) := by
          rw [Finset.sum_range_succ]
          rfl
        rw [hsucc]
        exact ih.add (hBcompact n)
  have htend : Filter.Tendsto (fun N ↦ ∑ m ∈ Finset.range N, B m)
      Filter.atTop (nhds (∑' m, B m)) := hBsummable.hasSum.tendsto_sum_nat
  have hS : (∑' m, B m) ∈ {f : K →L[ℂ] H | IsCompactOperator f} :=
    isClosed_setOf_isCompactOperator.mem_of_tendsto htend
      (Filter.Eventually.of_forall hpartial)
  simp only [Set.mem_setOf_eq] at hS
  rwa [hSD] at hS

end

end ShulmanFill
end GroupApproximation
