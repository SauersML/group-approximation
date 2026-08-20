import GroupApproximation.Kazhdan.OrbitAverageSpectralGap

/-!
# The criterion at the quadratic form, which is where eigenvalues live

`Kazhdan/OrbitAverageSpectralGap.lean` states its criterion as a bound on the
*norm* of the orbit average.  That is the right statement to compare with
`IsKazhdanPair.norm_orbitAverage_le`, and the wrong one to receive a spectral
estimate: `λ₁` of a graph Laplacian is a bound on the Rayleigh quotient
`⟪Δ x, x⟫ / ‖x‖²`, and turning a Rayleigh bound into a norm bound needs the
operator to be self-adjoint --- an extra hypothesis, and one that a
representation-theoretic average only satisfies when the alphabet is symmetric.

This module removes that step.  `WeightedFormGap` asks only for the Rayleigh
bound, and `isKazhdanPair_of_weightedFormGap` derives a Kazhdan pair from it
directly, with **no** self-adjointness, positivity or symmetry hypothesis
anywhere.  The reason it works is that only one inequality is ever needed of the
average --- that a nearly fixed vector has `⟪A x, x⟫` near `‖x‖²` --- and that
inequality is Cauchy--Schwarz applied to `A x - x`, which does not care what
kind of operator `A` is.

`weightedFormGap_of_weightedAverageGap` records that the form gap is the weaker
hypothesis of the two, so this criterion subsumes the norm one and nothing is
lost by stating a Żuk-type or Garland-type conclusion in this shape.
-/

namespace GroupApproximation
namespace SpectralGap

universe u v

/-- **A uniform gap for the quadratic form of a weighted orbit average.**  In
every complete orthogonal representation with no nonzero invariant vector, the
Rayleigh quotient of the weighted average is at most `lam`.

This is the conclusion of a spectral estimate: it bounds `⟪A x, x⟫` and says
nothing about `‖A x‖`, which is exactly the information an eigenvalue bound
carries. -/
def WeightedFormGap (G : Type u) [Group G] (S : Finset G) (w : G → ℝ)
    (lam : ℝ) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E],
    ∀ ρ : G →* (E ≃ₗᵢ[ℝ] E), IsKazhdanPair.HasNoInvariantVectors G ρ →
      ∀ x : E, inner ℝ (weightedAverage S w ρ x) x ≤ lam * ‖x‖ ^ 2

variable {G : Type u} [Group G]

/-- **A norm gap is a form gap**, by Cauchy--Schwarz.  So the criterion below is
strictly more general than `isKazhdanPair_of_weightedAverageGap`, and the two
tolerances agree. -/
theorem weightedFormGap_of_weightedAverageGap {S : Finset G} {w : G → ℝ}
    {lam : ℝ} (h : WeightedAverageGap.{u, v} G S w lam) :
    WeightedFormGap.{u, v} G S w lam := by
  intro E _ _ _ ρ hno x
  calc inner ℝ (weightedAverage S w ρ x) x
      ≤ ‖weightedAverage S w ρ x‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ (lam * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (h E ρ hno x) (norm_nonneg x)
    _ = lam * ‖x‖ ^ 2 := by ring

/-- **A uniform Rayleigh gap is a Kazhdan pair.**

Let `x` be a unit vector moved by at most `(1 - lam)/2` by every element of `S`.
Then the weighted average moves it by at most that much as well
(`norm_weightedAverage_sub_le`), so by Cauchy--Schwarz

```
    ⟪A x, x⟫ = ‖x‖² + ⟪A x - x, x⟫ ≥ 1 - (1 - lam)/2 = (1 + lam)/2 > lam,
```

which the gap forbids in a representation without invariant vectors.

No hypothesis is placed on the operator: `A` is not assumed self-adjoint, `S` is
not assumed symmetric or to generate `G`, and the weights need only be a
probability vector on `S`. -/
theorem isKazhdanPair_of_weightedFormGap {S : Finset G} {w : G → ℝ}
    (hw0 : ∀ q ∈ S, 0 ≤ w q) (hw1 : ∑ q ∈ S, w q = 1)
    {lam : ℝ} (hlam : lam < 1) (hgap : WeightedFormGap.{u, v} G S w lam) :
    IsKazhdanPair.{u, v} G S ((1 - lam) / 2) := by
  have hε : (0 : ℝ) < (1 - lam) / 2 := by linarith
  refine IsKazhdanPair.of_noInvariant_displacement hε ?_
  intro E _ _ _ ρ hno x hx
  by_contra hcon
  have hnear : ∀ q ∈ S, ‖ρ q x - x‖ ≤ (1 - lam) / 2 := fun q hq ↦
    le_of_lt (lt_of_not_ge (fun hge ↦ hcon ⟨q, hq, hge⟩))
  have hsub : ‖weightedAverage S w ρ x - x‖ ≤ (1 - lam) / 2 :=
    norm_weightedAverage_sub_le hw0 hw1 ρ x hnear
  have hgapx : inner ℝ (weightedAverage S w ρ x) x ≤ lam := by
    have hbound := hgap E ρ hno x
    rwa [hx, one_pow, mul_one] at hbound
  have hsplit : inner ℝ (weightedAverage S w ρ x) x
      = ‖x‖ ^ 2 + inner ℝ (weightedAverage S w ρ x - x) x := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
    ring
  have hcs : |inner ℝ (weightedAverage S w ρ x - x) x| ≤
      ‖weightedAverage S w ρ x - x‖ * ‖x‖ :=
    abs_real_inner_le_norm _ _
  have hprod : ‖weightedAverage S w ρ x - x‖ * ‖x‖ ≤ (1 - lam) / 2 := by
    rw [hx, mul_one]
    exact hsub
  have hlow : -((1 - lam) / 2) ≤ inner ℝ (weightedAverage S w ρ x - x) x := by
    have habs := abs_le.mp hcs
    linarith [habs.1]
  rw [hx, one_pow] at hsplit
  linarith

/-- **A uniform Rayleigh gap is property `(T)`.**  This is the statement that a
formalization of Żuk's criterion, or of Garland's method, would discharge:
its hypothesis is an eigenvalue inequality for one explicitly given operator,
and its conclusion is property `(T)` with an explicit Kazhdan pair. -/
theorem hasKazhdanPropertyT_of_weightedFormGap {S : Finset G} {w : G → ℝ}
    (hw0 : ∀ q ∈ S, 0 ≤ w q) (hw1 : ∑ q ∈ S, w q = 1)
    {lam : ℝ} (hlam : lam < 1) (hgap : WeightedFormGap.{u, v} G S w lam) :
    HasKazhdanPropertyT.{u, v} G :=
  ⟨S, (1 - lam) / 2, isKazhdanPair_of_weightedFormGap hw0 hw1 hlam hgap⟩

end SpectralGap
end GroupApproximation
