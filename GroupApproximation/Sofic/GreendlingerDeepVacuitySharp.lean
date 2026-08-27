import GroupApproximation.Sofic.GreendlingerDeepVacuity
import GroupApproximation.Sofic.GreendlingerSharpTwins

/-!
# The junction kill, read at the sharp constant

`GreendlingerDeepVacuity` proves `not_deep_confined`: a head block that runs
deep and stops inside the adjacent palindrome cannot occur in a minimal
expression.  That statement is phrased entirely in the half-form hypothesis set
— `6 * j < |t|` and `|c| + |t| < |M| + j` — and its conclusion is `False`.  Both
facts are what this file exploits: an impossibility has no bound to sharpen, and
the sharp offset hypothesis is *stronger* than the half-form one, so the single
argument discharges the `λ`-twin as well.

## The two brackets

Passing between the forms costs exactly two lemmas.

* `six_mul_lt_of_lam_lt` sends the sharp offset hypothesis to the half-form one:
  `(j : ℚ) < λ·|t|` with `λ ≤ 1/6` gives `6j < |t|`.  This is the direction the
  file needs, and it is the only direction available — the converse would want
  `1/6 ≤ λ`.
* `metricSmallCancellation_of_le` sends `C'(λ)` to `C'(1/6)`, which is the
  constant every piece bound inside `not_deep_confined` is read at.  The sharp
  assembly hands its residuals `MetricSmallCancellation R lam`, so this is the
  adapter that lets the junction kill be called from there.

Nothing else moves.  `deepArcSourceSharp_of_deepOverrunArcSharp` is the same
five-leaf case analysis as `deepArcSource_of_deepOverrunArc`, calling the same
`not_deep_confined`, with the arc bound carried through untouched.

## The deep regime is sharper than five sixths

At the sharp constant the deep hypotheses give more than they did at `1/6`.
`one_sub_lam_mul_lt_eaten` reads them as

    (1 − λ)·|t| < |E|,

against `5|t| < 6|E|` at the half form; at `λ = 1/6` the two agree and below it
the sharp one is strictly stronger.  The consequence is worth recording, because
it settles one of the two landing pads outright: the sharp conclusion asks for an
arc longer than `(1 − 3λ)·|r|`, and

    (1 − 3λ)·|t| ≤ (1 − λ)·|t| < |E|,

so **the eaten stretch of a deep block always clears the sharp bound**, with
slack `2λ·|t|` to spare.  `greendlingerAtSharp_of_deep_arc` is that statement:
wherever the reappearance copy of `GreendlingerBetaBranch` lands late enough, it
is a sharp arc, at every `λ` in range and with no further hypothesis.  This is
the sense in which the overrun configuration pins `1 − 3λ` from the arc side:
the deep block's own stretch is the arc, and `2λ` is the whole of the room.

The other pad, `greendlingerAtSharp_of_untouched_rotation`, needs only `0 < λ`,
which `GreendlingerSharpTwins.lam_pos_of_metric` supplies on any nondegenerate
family.

## The interface note

`not_deep_confined` needs `∀ r ∈ R, r ≠ []`, through
`GreendlingerRegime.swallow_bound_of_minimal` and through the emptiness side
condition of `GreendlingerWeight.not_absorb_of_minimal`.  The half-form gate
carries that hypothesis anyway, but the sharp family assembly
(`cascadeLandingSharp_family_of_deepArcSharp_of_betaSharp`) does not, so the
theorems here take it explicitly.  It is not a new obligation: on any family
whose symmetrization has two distinct members it is
`GreendlingerDehn.ne_nil_of_metricSmallCancellation`, and the assembly has to
thread it either way.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The two brackets between the constants -/

/-- **The metric condition is monotone in its constant.**  A piece under `λ` is
a piece under anything larger, so a family designed at a small constant serves
every bound read at a larger one.

`BespokeRouterGateAssembly.metricSmallCancellation_mono` is the same statement
over the router's own two-letter alphabet; this is the version the gate lane
needs, over an arbitrary alphabet. -/
theorem metricSmallCancellation_of_le {R : Set (List (α × Bool))} {lam mu : ℚ}
    (hle : lam ≤ mu) (h : MetricSmallCancellation R lam) :
    MetricSmallCancellation R mu := by
  intro p hp w hw hpre
  have h1 := h p hp w hw hpre
  have h2 : lam * (w.length : ℚ) ≤ mu * (w.length : ℚ) :=
    mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)
  linarith

/-- **The sharp offset hypothesis implies the half-form one.**  Below `1/6` an
offset under `λ` times the rotation is an offset under a sixth of it.

This is what lets an impossibility proved in the half-form hypothesis set be
called from the sharp regime without restating it. -/
theorem six_mul_lt_of_lam_lt {lam : ℚ} (hlam : lam ≤ 1 / 6) {j : ℕ}
    {t : List (α × Bool)} (hj : (j : ℚ) < lam * (t.length : ℚ)) :
    6 * j < t.length := by
  have hle : lam * (t.length : ℚ) ≤ 1 / 6 * (t.length : ℚ) :=
    mul_le_mul_of_nonneg_right hlam (Nat.cast_nonneg _)
  have h6 : (6 : ℚ) * (j : ℚ) < (t.length : ℚ) := by linarith
  exact_mod_cast h6

/-! ## 2.  The deep regime, at the sharp constant -/

/-- **The sharp reading of the deep regime.**  The `λ`-twin of
`GreendlingerDeepArc.five_mul_lt_six_mul_eaten`: the block eats more than
`1 − λ` of the head rotation.

At `λ = 1/6` this is the five-sixths bound; below it, it is strictly
stronger. -/
theorem one_sub_lam_mul_lt_eaten {lam : ℚ} {c t M E : List (α × Bool)} {j : ℕ}
    (hM : M = E ++ FreeGroup.invRev c)
    (hj : (j : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + j) :
    (1 - lam) * (t.length : ℚ) < (E.length : ℚ) := by
  have hMlen : M.length = E.length + c.length := by
    rw [hM, List.length_append, FreeGroup.invRev_length]
  have hnat : t.length < E.length + j := by omega
  have hq : (t.length : ℚ) < (E.length : ℚ) + (j : ℚ) := by exact_mod_cast hnat
  linarith

/-! ## 3.  The sharp arc producers -/

/-- Prepending a block moves a located sharp arc later by the block's length. -/
theorem GreendlingerAtSharp.append_left {R : Set (List (α × Bool))} {lam : ℚ}
    {n : ℕ} {V : List (α × Bool)} (h : GreendlingerAtSharp R lam n V)
    (P : List (α × Bool)) :
    GreendlingerAtSharp R lam (P.length + n) (P ++ V) := by
  obtain ⟨A, u, C, hV, hlen, s, hs, hupre, hlt⟩ := h
  refine ⟨P ++ A, u, C, ?_, ?_, s, hs, hupre, hlt⟩
  · rw [hV]
    simp only [List.append_assoc]
  · rw [List.length_append]
    omega

/-- **An untouched rotation is a sharp arc.**  A whole nonempty symmetrized
relator beats `(1 − 3λ)` times its own length as soon as `λ` is positive, which
`lam_pos_of_metric` supplies on any nondegenerate family. -/
theorem greendlingerAtSharp_of_untouched_rotation {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam0 : 0 < lam) {s w A C : List (α × Bool)} {n : ℕ}
    (hs : s ∈ symmetrization R) (hsne : s ≠ [])
    (hw : w = A ++ s ++ C) (hn : n ≤ A.length) :
    GreendlingerAtSharp R lam n w := by
  refine ⟨A, s, C, hw, hn, s, hs, List.prefix_refl s, ?_⟩
  have hpos : (0 : ℚ) < (s.length : ℚ) := by
    have h := List.length_pos_iff.mpr hsne
    exact_mod_cast h
  have hml : (0 : ℚ) < lam * (s.length : ℚ) := mul_pos hlam0 hpos
  linarith

/-- **The eaten stretch of a deep block is a sharp arc.**  A suffix of a
rotation longer than `(1 − λ)` of it prefixes another rotation of the same
relator, and `(1 − 3λ) ≤ (1 − λ)` for every nonnegative `λ`, so the bound the
sharp conclusion asks for is already met — with `2λ·|t|` to spare.

So the reappearance copy of
`GreendlingerBetaBranch.palindrome_eq_append_reappearance` closes the sharp goal
wherever it lands late enough, at every constant in range.  Feed `hbound` from
`one_sub_lam_mul_lt_eaten`. -/
theorem greendlingerAtSharp_of_deep_arc {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 ≤ lam) {t E w A C : List (α × Bool)} {n : ℕ}
    (ht : t ∈ symmetrization R) (hEt : E <:+ t)
    (hbound : (1 - lam) * (t.length : ℚ) < (E.length : ℚ))
    (hw : w = A ++ E ++ C) (hn : n ≤ A.length) :
    GreendlingerAtSharp R lam n w := by
  obtain ⟨z, hz⟩ := hEt
  have hrot : t.rotate z.length = E ++ z := by
    rw [← hz]
    exact rotate_append z E
  refine ⟨A, E, C, hw, hn, t.rotate z.length,
    rotate_mem_symmetrization ht z.length, ?_, ?_⟩
  · rw [hrot]
    exact ⟨z, rfl⟩
  · rw [List.length_rotate]
    have hmono : (1 - 3 * lam) * (t.length : ℚ)
        ≤ (1 - lam) * (t.length : ℚ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    linarith

/-! ## 4.  The sharp residual, and the reduction to it -/

/-- **The `λ`-twin of `GreendlingerDeepVacuity.DeepOverrunArc`.**  The same
predicate with the offset hypothesis and the arc bound moved to the sharp
constant, and with the junction case excluded exactly as there: the prefix the
head's block destroys is not confined to the adjacent palindrome.

The non-confinement hypothesis is `λ`-free, and so is every other field except
the two that carry the constant — which is the whole point: one impossibility
argument serves both residuals. -/
def DeepOverrunArcSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t c' t' M B' : List (α × Bool))
    (f : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α) (j : ℕ),
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: f) g →
    t ∈ symmetrization R → t' ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c' t') →
    M <:+ palindrome c t →
    (conjEval ((FreeGroup.mk c', t') :: f)).toWord
      = FreeGroup.invRev M ++ B' →
    ¬ (FreeGroup.invRev M <+: palindrome c' t') →
    c.length < M.length → (j : ℚ) < lam * (t.length : ℚ) →
    c.length + t.length < M.length + j →
    GreendlingerAtSharp R lam (M.length + j - (c.length + t.length)) B'

/-- **The sharp deep obligation, from the sharp overrun obligation.**

The twin of `GreendlingerDeepVacuity.deepTailArc_of_deepOverrunArc` composed
with `GreendlingerDeepArc.deepArcSource_of_deepTailArc`, run in one pass because
the sharp lane has no intermediate tail predicate.  The confined branch calls
`not_deep_confined` — the *same* theorem the half-form route calls, with the
offset hypothesis cast down by `six_mul_lt_of_lam_lt` and the constant raised by
`metricSmallCancellation_of_le`. -/
theorem deepArcSourceSharp_of_deepOverrunArcSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R lam)
    (h : DeepOverrunArcSharp R lam) : DeepArcSourceSharp R lam := by
  intro c t e g P' M B' j hmin ht hredp heq htail hlow hj hgt
  have hj6 : 6 * j < t.length := six_mul_lt_of_lam_lt hlam hj
  have hlenP : P'.length + M.length = c.length + t.length + c.length := by
    have hb := congrArg List.length heq
    rw [List.length_append, length_palindrome] at hb
    exact hb.symm
  obtain ⟨c', t', f, ht', hredp', hmin', hev, -⟩ :=
    exists_deep_tail_setup hR hRne hmin htail hlow
  rw [← hev] at htail
  by_cases hconf : FreeGroup.invRev M <+: palindrome c' t'
  · exfalso
    obtain ⟨B'', hB''⟩ := hconf
    exact not_deep_confined hRne (metricSmallCancellation_of_le hlam hmetric)
      hmin' ht ht' hredp hredp' heq hB''.symm hlow hj6 hgt
  · refine ((h c t c' t' M B' f g j hmin' ht ht' hredp hredp' ⟨P', heq.symm⟩
      htail hconf hlow hj hgt).append_left P').mono ?_
    omega

/-! ## 5.  The sharp gate, through the residual -/

/-- `CascadeLandingSharp` from the sharp overrun obligation and the sharp
landing production. -/
theorem cascadeLandingSharp_of_deepOverrunArcSharp_of_landingSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepOverrunArcSharp R lam)
    (hland : LandingProductionSharp R lam) :
    CascadeLandingSharp R lam :=
  cascadeLandingSharp_of_deepArcSharp_of_landingSharp
    (deepArcSourceSharp_of_deepOverrunArcSharp hlam hR hRne hmetric hdeep) hland

/-- **`CascadeLandingSharp` over the two live residuals.**  The sharp overrun
obligation on the deep side and the (β) landing production on the other, which
is the pair `GreendlingerSharpTwins.cascadeLandingSharp_of_deepArcSharp_of_betaSharp`
is stated over — with the deep half now costing only the overrun. -/
theorem cascadeLandingSharp_of_deepOverrunArcSharp_of_betaSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepOverrunArcSharp R lam)
    (hbeta : LandingProductionBetaSharp R lam) :
    CascadeLandingSharp R lam :=
  cascadeLandingSharp_of_deepOverrunArcSharp_of_landingSharp hlam hR hRne
    hmetric hdeep (landingProductionSharp_of_betaSharp hmetric hbeta)

end SmallCancellationRouter
end GroupApproximation
