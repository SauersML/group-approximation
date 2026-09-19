import GroupApproximation.Analysis.CalkinSchauder

/-!
# Schauder's theorem in Hilbert space, with the residual discharged

`Analysis/CalkinSchauder` reduces `CalkinAlgebra.CompactStarClosedStatement` —
the adjoint of a compact operator is compact, which is what makes the compacts
a `*`-closed ideal and so gives the Calkin algebra a star — to the single
residual

    `CompactOfStarMulSelfStatement` : `S*S` compact implies `S` compact.

This module proves that residual, so both statements become theorems and the
Calkin algebra's star is unconditional.

## The proof

Two steps, and neither uses polar decomposition, functional calculus or
finite-rank approximation, none of which the pinned Mathlib carries for
`IsCompactOperator`.

1. **The pointwise bound.**  `⟪(S*S)x, x⟫ = ⟪Sx, Sx⟫`, so by Cauchy--Schwarz

       `‖S x‖² = ‖⟪(S*S)x, x⟫‖ ≤ ‖(S*S)x‖ ‖x‖` .

   Applied to `x - y` this says that `S` is Hölder-`1/2` in `S*S`: for `x`, `y`
   in the unit ball, `‖Sx - Sy‖² ≤ 2 ‖(S*S)x - (S*S)y‖`.

2. **Total boundedness transfers along that bound.**  `S*S` compact makes
   `(S*S)''B` totally bounded, `B` the unit ball.  Cover it by finitely many
   balls of radius `ε²/8`; two points of `B` whose `(S*S)`-images share a ball
   have `‖(S*S)x - (S*S)y‖ ≤ ε²/4`, hence `‖Sx - Sy‖² ≤ ε²/2 < ε²`.  Choosing
   one preimage per centre therefore gives a finite `ε`-net of `S''B`, so
   `S''B` is totally bounded and its closure — complete, because `H` is — is
   compact.

The estimate is the whole content; the neighbourhood form of
`IsCompactOperator` is reached through
`isCompactOperator_iff_image_ball_subset_compact`, the same route
`Analysis/CompactIntegralOperator` uses.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.  The names it uses that have no other
precedent in the repository, and so are where the first build should look first,
are `isCompact_iff_totallyBounded_isComplete`, `IsClosed.isComplete`,
`TotallyBounded.closure`, `TotallyBounded.subset`, `IsCompact.totallyBounded`
and `Metric.totallyBounded_iff`.
-/

namespace GroupApproximation
namespace CalkinAlgebra

open scoped InnerProductSpace

noncomputable section

/-- **The pointwise Cauchy--Schwarz bound.**  `‖S x‖² ≤ ‖(S*S)x‖ ‖x‖`, from
`⟪(S*S)x, x⟫ = ⟪Sx, Sx⟫`. -/
theorem norm_apply_sq_le_starMulSelf {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : H →L[ℂ] H) (x : H) :
    ‖S x‖ ^ 2 ≤ ‖(star S * S) x‖ * ‖x‖ := by
  have hmul : (star S * S) x = (ContinuousLinearMap.adjoint S) (S x) := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    rfl
  have hinner : ⟪(star S * S) x, x⟫_ℂ = ⟪S x, S x⟫_ℂ := by
    rw [hmul]
    exact ContinuousLinearMap.adjoint_inner_left S x (S x)
  have hsq : ‖S x‖ ^ 2 = ‖⟪S x, S x⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp
  rw [hsq, ← hinner]
  exact norm_inner_le_norm _ _

/-- **The residual of `Analysis/CalkinSchauder`, proved.**  On a Hilbert space
an operator is compact as soon as `S*S` is. -/
theorem compactOfStarMulSelf : CompactOfStarMulSelfStatement := by
  classical
  intro H _ _ _ S hSS
  have hSS' : IsCompactOperator ((star S * S : H →L[ℂ] H).toLinearMap) := hSS
  obtain ⟨K, hK, hKsub⟩ :=
    (isCompactOperator_iff_image_ball_subset_compact
      (star S * S : H →L[ℂ] H).toLinearMap one_pos).mp hSS'
  have hTsub :
      (fun z : H ↦ (star S * S) z) '' Metric.ball (0 : H) 1 ⊆ K := hKsub
  have hTtb :
      TotallyBounded ((fun z : H ↦ (star S * S) z) '' Metric.ball (0 : H) 1) :=
    hK.totallyBounded.subset hTsub
  have hStb : TotallyBounded ((fun z : H ↦ S z) '' Metric.ball (0 : H) 1) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    have hρ : (0 : ℝ) < ε ^ 2 / 8 := by positivity
    obtain ⟨t, ht, htsub⟩ := (Metric.totallyBounded_iff.mp hTtb) (ε ^ 2 / 8) hρ
    set g : H → H := fun y : H ↦
      if h : ∃ z : H, z ∈ Metric.ball (0 : H) 1 ∧
          (star S * S) z ∈ Metric.ball y (ε ^ 2 / 8)
        then S h.choose else 0 with hg
    refine ⟨g '' t, ht.image _, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hmem : (star S * S) x ∈ ⋃ y ∈ t, Metric.ball y (ε ^ 2 / 8) :=
      htsub ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hmem
    have hPy : ∃ z : H, z ∈ Metric.ball (0 : H) 1 ∧
        (star S * S) z ∈ Metric.ball y (ε ^ 2 / 8) := ⟨x, hx, hxy⟩
    have hfy : g y = S hPy.choose := by
      rw [hg]
      exact dif_pos hPy
    have hspec := hPy.choose_spec
    set x' := hPy.choose
    obtain ⟨hx'mem, hTx'mem⟩ := hspec
    refine Set.mem_iUnion₂.mpr ⟨g y, ⟨y, hy, rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, hfy]
    have hxnorm : ‖x‖ < 1 := by
      have hb := Metric.mem_ball.mp hx
      rwa [dist_zero_right] at hb
    have hx'norm : ‖x'‖ < 1 := by
      have hb := Metric.mem_ball.mp hx'mem
      rwa [dist_zero_right] at hb
    have hdiff : ‖x - x'‖ ≤ 2 := by
      have h := norm_sub_le x x'
      linarith
    have hTdist :
        ‖(star S * S) x - (star S * S) x'‖ ≤ ε ^ 2 / 4 := by
      have h1 : dist ((star S * S) x) y < ε ^ 2 / 8 := Metric.mem_ball.mp hxy
      have h2 : dist ((star S * S) x') y < ε ^ 2 / 8 :=
        Metric.mem_ball.mp hTx'mem
      have h3 := dist_triangle ((star S * S) x) y ((star S * S) x')
      rw [dist_comm y ((star S * S) x')] at h3
      have h4 : dist ((star S * S) x) ((star S * S) x') ≤ ε ^ 2 / 4 := by
        linarith
      rwa [dist_eq_norm] at h4
    have hkey : ‖S x - S x'‖ ^ 2 ≤
        ‖(star S * S) x - (star S * S) x'‖ * ‖x - x'‖ := by
      have h := norm_apply_sq_le_starMulSelf S (x - x')
      rw [map_sub S x x', map_sub (star S * S) x x'] at h
      exact h
    have hprod : ‖(star S * S) x - (star S * S) x'‖ * ‖x - x'‖ ≤
        (ε ^ 2 / 4) * 2 :=
      mul_le_mul hTdist hdiff (norm_nonneg _) (by positivity)
    have hlt : ‖S x - S x'‖ ^ 2 < ε ^ 2 := by
      have hpos : (0 : ℝ) < ε ^ 2 := by positivity
      linarith
    by_contra hcon
    push Not at hcon
    nlinarith [hlt, hcon, hε.le, norm_nonneg (S x - S x')]
  have hStb' :
      TotallyBounded ((S : H →L[ℂ] H).toLinearMap '' Metric.ball (0 : H) 1) :=
    hStb
  have key : IsCompactOperator ((S : H →L[ℂ] H).toLinearMap) := by
    refine (isCompactOperator_iff_image_ball_subset_compact
      (S : H →L[ℂ] H).toLinearMap one_pos).mpr ?_
    refine ⟨closure ((S : H →L[ℂ] H).toLinearMap '' Metric.ball (0 : H) 1),
      ?_, subset_closure⟩
    rw [isCompact_iff_totallyBounded_isComplete]
    exact ⟨hStb'.closure, isClosed_closure.isComplete⟩
  exact key

/-- **Schauder's theorem in Hilbert space**, now a theorem: the adjoint of a
compact operator is compact.  This is what
`Analysis/CalkinAlgebra.isStarIdeal_of_compactStarClosed` consumes, so the
Calkin algebra's `Star`, `StarRing` and `StarModule` structure no longer rests
on a hypothesis. -/
theorem compactStarClosed : CompactStarClosedStatement :=
  compactStarClosed_of_compactOfStarMulSelf compactOfStarMulSelf

/-- The adjoint form, at one operator. -/
theorem isCompactOperator_star {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H}
    (hT : IsCompactOperator T) : IsCompactOperator (star T : H →L[ℂ] H) :=
  compactStarClosed H T hT

end

end CalkinAlgebra
end GroupApproximation
