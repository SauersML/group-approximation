import GroupApproximation.Analysis.VoiculescuGlimmCompression

/-!
# (V2) The spectral bound: what a state that kills the compacts can be

The third piece of Glimm's lemma bounds the state.  The classical phrasing is
that `ρ(b)` lies below the top of the *essential* spectrum of `b`, and the
obvious formalisation would introduce that notion — neither the tree nor the
pinned Mathlib has it, and defining it would mean spectral theory in the Calkin
algebra before any of it could be used.

None of that is needed.  Two facts compose to give the bound in the form the
rest of the proof consumes, and neither mentions a spectrum:

* a positive unital functional cannot exceed a bound that the *order* already
  records: `x ≤ t • 1` forces `re ρ(x) ≤ t`, because `t • 1 - x` is positive and
  `ρ` sends positives to nonnegative reals;
* `ρ` does not see a compact compression:
  `ρ((1-e) b (1-e)) = ρ(b)` exactly, for every compact `e`, which is
  `Analysis/VoiculescuGlimmCompression`.

Composed: `re ρ(b) ≤ t` as soon as *some* compact compression of `b` is bounded
by `t`.  That is the whole content of "the state only sees `b` essentially".
Compressing by `1 - e` moves `b` arbitrarily far in norm while leaving `ρ(b)`
fixed, so every compression is a bound on the state at once, and the state's
values become essential quantities — quantities that no finite-rank part of `b`
can influence.

The bridge to vectors, which (V2)'s remaining pieces need, is then free rather
than another theorem: the Loewner order on `B(H)` is *definitionally* positivity
of the difference, so `x ≤ t • 1` is exactly the statement that
`re ⟪η, x η⟫ ≤ t ‖η‖²` for every `η`.  A hypothesis about vectors orthogonal to a
subspace is therefore already a hypothesis about a compression, with no
translation step in between.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **A positive unital functional respects the order bound.**  If `x` is below
`t • 1` then `ρ x` is below `t`.  No spectrum, no norm: the order records the
bound and positivity reads it off. -/
theorem re_apply_le_of_le_smul_one (ρ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hpos : ∀ T : H →L[ℂ] H, 0 ≤ T → ∃ r : ℝ, 0 ≤ r ∧ ρ T = r)
    (hone : ρ 1 = 1) {x : H →L[ℂ] H} {t : ℝ}
    (hx : x ≤ (t : ℂ) • (1 : H →L[ℂ] H)) : (ρ x).re ≤ t := by
  have hsub : (0 : H →L[ℂ] H) ≤ (t : ℂ) • (1 : H →L[ℂ] H) - x :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hx
  obtain ⟨r, hr0, hr⟩ := hpos _ hsub
  have hlin : ρ ((t : ℂ) • (1 : H →L[ℂ] H) - x) = (t : ℂ) - ρ x := by
    rw [map_sub, map_smul, smul_eq_mul, hone, mul_one]
  rw [hlin] at hr
  have hre := congrArg Complex.re hr
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  linarith

omit [CompleteSpace H] in
/-- **The spectral bound.**  A state annihilating the compacts is bounded by any
compact compression of its argument.

This is the sense in which such a state sees only the essential part of `b`: the
compression `(1-e) b (1-e)` can be moved arbitrarily far from `b` in norm by
choosing `e`, and every one of those compressions bounds `ρ(b)`. -/
theorem re_apply_le_of_compress_le (ρ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hpos : ∀ T : H →L[ℂ] H, 0 ≤ T → ∃ r : ℝ, 0 ≤ r ∧ ρ T = r)
    (hone : ρ 1 = 1)
    (hK : ∀ T : H →L[ℂ] H, IsCompactOperator T → ρ T = 0)
    {e b : H →L[ℂ] H} (he : IsCompactOperator e) {t : ℝ}
    (hb : (1 - e) * b * (1 - e) ≤ (t : ℂ) • (1 : H →L[ℂ] H)) :
    (ρ b).re ≤ t := by
  have hcomp : ρ ((1 - e) * b * (1 - e)) = ρ b :=
    apply_compress_eq_of_annihilates_compacts ρ hK e b he
  have h := re_apply_le_of_le_smul_one ρ hpos hone hb
  rwa [hcomp] at h

omit [CompleteSpace H] in
/-- **The order bound is a statement about vectors.**  Included because the
remaining pieces of (V2) consume it in that direction, and because the Loewner
order makes it free: `x ≤ t • 1` unfolds to positivity of the difference, whose
quadratic form is `t ‖η‖² - re ⟪η, x η⟫`. -/
theorem re_inner_le_of_le_smul_one {x : H →L[ℂ] H} {t : ℝ}
    (hx : x ≤ (t : ℂ) • (1 : H →L[ℂ] H)) (η : H) :
    RCLike.re ⟪η, x η⟫_ℂ ≤ t * ‖η‖ ^ 2 := by
  have hpos : ((t : ℂ) • (1 : H →L[ℂ] H) - x).IsPositive := hx
  have h := hpos.re_inner_nonneg_right η
  have hone_apply : (1 : H →L[ℂ] H) η = η := rfl
  have hsplit : ⟪η, ((t : ℂ) • (1 : H →L[ℂ] H) - x) η⟫_ℂ
      = (t : ℂ) * ⟪η, η⟫_ℂ - ⟪η, x η⟫_ℂ := by
    rw [sub_apply, inner_sub_right, smul_apply,
      hone_apply, inner_smul_right]
  rw [hsplit, map_sub] at h
  have hself : RCLike.re ((t : ℂ) * ⟪η, η⟫_ℂ) = t * ‖η‖ ^ 2 := by
    have h2 : ⟪η, η⟫_ℂ = ((‖η‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K η
    rw [h2, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  rw [hself] at h
  linarith

end

end ShulmanFill
end GroupApproximation
