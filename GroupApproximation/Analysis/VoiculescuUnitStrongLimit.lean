import GroupApproximation.Analysis.VoiculescuSequentialUnit

/-!
# A sequential approximate unit converges strongly to the identity

`SequentialCompactUnit` records absorption in norm against compact operators.
The partition of unity needs the weaker-looking but differently-shaped fact that
`e_n x → x` for every vector, and it does not follow from absorption by any
formal manipulation — one has to produce a compact operator that sees `x`.

The rank-one operator `T y = ⟪x, y⟫ x` is that operator.  It is compact because
it factors through `ℂ`, which is locally compact, and `T x = ‖x‖² x`, so

    `‖x‖² ‖x - e_n x‖ = ‖(T - e_n T) x‖ ≤ ‖T - e_n T‖ ‖x‖` ,

and absorption of `T` gives the claim after dividing by `‖x‖`, with `x = 0`
handled separately.

This is the second half of `QuasicentralPartition.tendsto_sum_sq`: the first is
`MonotoneCompactUnit.sum_pieceSqrt_sq`, which says the partial sums of the
squares are the members of the unit.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology
open scoped InnerProductSpace

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The rank-one operator `y ↦ ⟪x, y⟫ x`. -/
def rankOneSelf (x : H) : H →L[ℂ] H := (innerSL ℂ x).smulRight x

omit [CompleteSpace H] in
@[simp] theorem rankOneSelf_apply (x y : H) : rankOneSelf x y = ⟪x, y⟫_ℂ • x := rfl

omit [CompleteSpace H] in
/-- A rank-one operator is compact: it factors through `ℂ`. -/
theorem isCompactOperator_rankOneSelf (x : H) :
    IsCompactOperator ((rankOneSelf x : H →L[ℂ] H)) := by
  have h : IsCompactOperator ((innerSL ℂ x : H →L[ℂ] ℂ)) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  have heq : (rankOneSelf x : H →L[ℂ] H)
      = (ContinuousLinearMap.toSpanSingleton ℂ x).comp (innerSL ℂ x) := by
    ext y
    simp [rankOneSelf, ContinuousLinearMap.toSpanSingleton]
  rw [heq]
  exact h.clm_comp (ContinuousLinearMap.toSpanSingleton ℂ x)

/-- **A sequential approximate unit for the compacts converges strongly to the
identity.** -/
theorem SequentialCompactUnit.tendsto_apply (u : SequentialCompactUnit H) (x : H) :
    Tendsto (fun n ↦ u.toFun n x) atTop (𝓝 x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact Tendsto.congr (fun n ↦ ((u.toFun n).map_zero).symm) tendsto_const_nhds
  · have habs := u.tendsto_left (rankOneSelf x) (isCompactOperator_rankOneSelf x)
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hinner : ⟪x, x⟫_ℂ = ((‖x‖ : ℂ) ^ 2) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    have hb : ∀ n, ‖u.toFun n x - x‖
        ≤ ‖rankOneSelf x - u.toFun n * rankOneSelf x‖ * ‖x‖⁻¹ := by
      intro n
      have h1 : (u.toFun n * rankOneSelf x) x = u.toFun n (rankOneSelf x x) := rfl
      have h2 : (rankOneSelf x - u.toFun n * rankOneSelf x) x
          = rankOneSelf x x - (u.toFun n * rankOneSelf x) x := rfl
      have hkey : (rankOneSelf x - u.toFun n * rankOneSelf x) x
          = ((‖x‖ : ℂ) ^ 2) • (x - u.toFun n x) := by
        rw [h2, h1, rankOneSelf_apply, hinner, map_smul, smul_sub]
      have hop : ‖(rankOneSelf x - u.toFun n * rankOneSelf x) x‖
          ≤ ‖rankOneSelf x - u.toFun n * rankOneSelf x‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      rw [hkey, norm_smul, norm_sub_rev] at hop
      have hnorm : ‖x‖ ^ 2 * ‖u.toFun n x - x‖
          ≤ ‖rankOneSelf x - u.toFun n * rankOneSelf x‖ * ‖x‖ := by
        simpa using hop
      rw [← div_eq_mul_inv, le_div_iff₀ hxpos]
      refine le_of_mul_le_mul_left ?_ hxpos
      calc ‖x‖ * (‖u.toFun n x - x‖ * ‖x‖)
          = ‖x‖ ^ 2 * ‖u.toFun n x - x‖ := by ring
        _ ≤ ‖rankOneSelf x - u.toFun n * rankOneSelf x‖ * ‖x‖ := hnorm
        _ = ‖x‖ * ‖rankOneSelf x - u.toFun n * rankOneSelf x‖ := by ring
    have hz : Tendsto
        (fun n ↦ ‖rankOneSelf x - u.toFun n * rankOneSelf x‖ * ‖x‖⁻¹) atTop (𝓝 0) := by
      simpa using habs.mul_const (‖x‖⁻¹)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n ↦ norm_nonneg _) hb hz

end

end ShulmanFill
end GroupApproximation
