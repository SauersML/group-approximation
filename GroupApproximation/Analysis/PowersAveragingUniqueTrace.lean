import GroupApproximation.Analysis.PowersAveraging
import GroupApproximation.Manuscript.MFRecognition.TensorSynchronizationData

/-!
# Powers averaging gives the unique trace, not only simplicity

`Analysis/PowersAveraging` proves component (D) of Powers' argument: the
averaging estimate makes `C*_r(G)` simple.  This module proves that the *same*
estimate makes the canonical trace the **only** tracial state.

## Why this matters for `cor:regular-nonmf-algebra`

Dahmani--Guirardel--Osin's Theorem 2.35 asserts two things, simplicity and
uniqueness of the trace.  `Manuscript/NonMF/DGOTheorem235Slice` reduces it to
four named citations, one of which,
`BKKOUniqueTraceOfCStarSimple` — Breuillard--Kalantar--Kennedy--Ozawa's
Theorem 1.3, *"every C*-simple group has the unique trace property"* — carries
the second conclusion alone.  That citation is a deep theorem: the implication
"C⋆-simple ⇒ unique trace" runs through the triviality of the amenable radical
and Furstenberg boundary theory.

It is not needed.  Powers averaging is a *quantitative* statement, and it gives
both conclusions by the same three lines, because a tracial state is invariant
under conjugation by the canonical unitaries:

    σ(λ(g) a λ(g)⋆) = σ(λ(g)⋆ λ(g) a) = σ(a),

so `σ` is unchanged by averaging, while averaging drives an element of
`ker τ₀` into a ball of radius `ε`; and `|σ(y)| ≤ ‖y‖` for a tracial state on a
unital C⋆-algebra.  Hence `σ` kills `ker τ₀`, and since `σ(1) = τ₀(1) = 1` and
`x - τ₀(x)·1 ∈ ker τ₀`, `σ = τ₀` outright.

The only external ingredient is the boundedness of a tracial state,
`Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le`, which is
landed and proved through Mathlib's GNS construction.

## What is *not* claimed

Nothing here proves the averaging estimate.  `PowersAveragingEstimate G` is a
hypothesis of every statement below, exactly as in `Analysis/PowersAveraging`.
What is established is that the estimate is a *single* sufficient input for both
halves of DGO 2.35, so the citation chain loses one classical theorem.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace ReducedGroupCStarTrace

universe u

variable (G : Type u) [Group G]

/-! ## A tracial state is invariant under conjugation by `λ(g)` -/

/-- **Conjugating by a canonical unitary does not move a tracial state.**

`σ(λ(g) a λ(g)⋆) = σ(λ(g)⋆ (λ(g) a)) = σ((λ(g)⋆ λ(g)) a) = σ(a)`; the first step
is traciality, the second associativity, the third unitarity of `λ(g)`.  This is
the only place where the group enters. -/
theorem tracialState_conj_reducedLeftRegular
    (σ : TracialState (ReducedGroupCStar G)) (g : G) (a : ReducedGroupCStar G) :
    σ (reducedLeftRegular G g * a * star (reducedLeftRegular G g)) = σ a := by
  have hunit : star (reducedLeftRegular G g) * reducedLeftRegular G g = 1 :=
    star_reducedLeftRegular_mul G g
  calc σ (reducedLeftRegular G g * a * star (reducedLeftRegular G g))
      = σ (star (reducedLeftRegular G g) * (reducedLeftRegular G g * a)) :=
        σ.map_mul_comm _ _
    _ = σ ((star (reducedLeftRegular G g) * reducedLeftRegular G g) * a) := by
        rw [mul_assoc]
    _ = σ a := by rw [hunit, one_mul]

/-- **Averaging by canonical unitaries does not move a tracial state.** -/
theorem tracialState_average (σ : TracialState (ReducedGroupCStar G))
    (n : ℕ) (hn : 0 < n) (g : Fin n → G) (a : ReducedGroupCStar G) :
    σ ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i))) = σ a := by
  have hlin : σ (∑ i : Fin n,
      reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)))
      = ∑ i : Fin n,
        σ (reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i))) :=
    map_sum σ.toLinearMap _ Finset.univ
  have hconst : ∑ i : Fin n,
      σ (reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)))
      = ∑ _i : Fin n, σ a :=
    Finset.sum_congr rfl fun i _ ↦ tracialState_conj_reducedLeftRegular G σ (g i) a
  have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [TracialState.map_smul, hlin, hconst, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne,
    one_mul]

/-! ## Averaging kills the kernel of the canonical trace -/

/-- **Every tracial state vanishes on the kernel of the canonical trace.**

`σ(a)` equals `σ` of every average of `a`, and the estimate makes some average
have norm at most `ε`; `|σ(y)| ≤ ‖y‖`, so `|σ(a)| ≤ ε` for every positive `ε`. -/
theorem tracialState_eq_zero_of_canonical_eq_zero (h : PowersAveragingEstimate G)
    (σ : TracialState (ReducedGroupCStar G)) (a : ReducedGroupCStar G)
    (ha : canonicalFaithfulTracialState G a = 0) : σ a = 0 := by
  have key : ∀ ε : ℝ, 0 < ε → ‖σ a‖ ≤ ε := by
    intro ε hε
    obtain ⟨n, g, hn, hbound⟩ := h a ha ε hε
    calc ‖σ a‖
        = ‖σ ((n : ℂ)⁻¹ • ∑ i : Fin n,
            reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)))‖ := by
          rw [tracialState_average G σ n hn g a]
      _ ≤ ‖(n : ℂ)⁻¹ • ∑ i : Fin n,
            reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i))‖ :=
          Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le σ _
      _ ≤ ε := hbound
  by_contra hne
  have hpos : 0 < ‖σ a‖ := norm_pos_iff.mpr hne
  have hhalf := key (‖σ a‖ / 2) (by linarith)
  linarith

/-! ## The canonical trace is the only tracial state -/

/-- **Powers averaging forces uniqueness of the trace.**

Every tracial state agrees with the canonical one.  Subtracting the scalar
`τ₀(x)·1` puts `x` inside `ker τ₀`, where the previous theorem applies, and both
functionals are unital. -/
theorem tracialState_eq_canonical_of_powersAveragingEstimate
    (h : PowersAveragingEstimate G) (σ : TracialState (ReducedGroupCStar G))
    (x : ReducedGroupCStar G) : σ x = canonicalFaithfulTracialState G x := by
  have ha : canonicalFaithfulTracialState G
      (x - canonicalFaithfulTracialState G x • (1 : ReducedGroupCStar G)) = 0 := by
    rw [FaithfulTracialState.map_sub, FaithfulTracialState.map_smul,
      FaithfulTracialState.apply_one, smul_eq_mul, mul_one, sub_self]
  have hσ := tracialState_eq_zero_of_canonical_eq_zero G h σ _ ha
  rw [TracialState.map_sub, TracialState.map_smul, TracialState.apply_one,
    smul_eq_mul, mul_one, sub_eq_zero] at hσ
  exact hσ

end ReducedGroupCStarTrace
end GroupApproximation

open GroupApproximation.ReducedGroupCStarTrace

#audit_axioms tracialState_conj_reducedLeftRegular
#audit_axioms tracialState_average
#audit_axioms tracialState_eq_zero_of_canonical_eq_zero
#audit_axioms tracialState_eq_canonical_of_powersAveragingEstimate
