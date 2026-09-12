import GroupApproximation.Sofic.GreendlingerSharpRigidity

/-!
# The back-side loss at an arbitrary constant

`GreendlingerDeepOverrunCount` §6 bounds what the *landing* factor's own block
eats out of its own rotation, in both orientations of the junction one step
further down.  Both statements are pinned at `λ = 1/6` for a single reason: they
close through `GreendlingerDeepestMatch.six_mul_intrusion_lt`, the double piece
bound with the denominator cleared, and therefore read
`MetricSmallCancellation R (1/6)` and conclude `6|E₃| < |t₃|`.

The double piece bound is already twinned —
`GreendlingerSharpTwins.intrusion_lt_of_metric` is the same three lines with the
`C'(λ)` hypothesis consumed rationally instead of cast down to `ℕ` — so both
back-side statements twin by substitution alone.  Nothing about the junction is
re-examined, because the constant never entered the junction: the distinctness
inputs (`GreendlingerCoincidence.invRev_ne_rotate_of_minimal` in the backward
orientation, `ne_rotate_invRev_of_minimal_forward` in the overrun one) are
statements about minimal expressions and name no constant at all, and the
rotation-offset conversion `eq_rotate_invRev_of_invRev_eq_rotate` is pure list
arithmetic.

No sign hypothesis on `λ` is read anywhere in this file.  `C'(λ)` is applied to
a piece that is genuinely a prefix of the relator it is measured against, so
there is no saturating branch of the kind
`GreendlingerSharpRigidity.intrusion_lt_of_forward_sharp` has to split off; the
eaten stretch `E₃` is handed over as an honest suffix of `t₃` by `hE`.

## The scope note carries over verbatim

The `λ`-free file records that `hintr` — the eaten stretch landing in the next
factor's relator territory — is exactly what fails when the landing factor's own
block overruns, so the back bound closes the back side only at a **shallow**
landing factor.  Twinning does not touch that: it moves a constant, not a
hypothesis.  `GreendlingerDeepInvariant`'s route does not need the back bound,
since it recurses inside the descent and hands a deep landing factor to its own
stage; only the front bound is load-bearing there, and the front bound is
`intrusion_lt_of_forward_sharp`.

## The orientation package

§4's `exists_deep_orientation` is twinned here too.  It is the one statement in
the deep-regime range whose `λ`-dependence is not the piece bound but the
five-sixths reading of the block, and that reading is already twinned as
`GreendlingerDeepVacuitySharp.one_sub_lam_mul_lt_eaten`, which gives the
strictly stronger `(1 − λ)|t| < |E|`.  Its other three conjuncts are word
geometry and are quoted unchanged.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The orientation package, at an arbitrary constant -/

/-- **The whole deep-regime geometry, at any `λ`.**  The `λ`-twin of
`GreendlingerDeepOverrunCount.exists_deep_orientation`.

Every structural conjunct is quoted verbatim — the block splits as
`E ++ invRev c`, its formal inverse as `c ++ invRev E`, the stretch `E` is a
suffix of the head rotation, and the overrun depth never exceeds the offset it
was launched with.  What moves is the offset hypothesis, `6j < |t|` becoming
`j < λ|t|`, and the eaten-fraction conjunct, `5|t| < 6|E|` becoming
`(1 − λ)|t| < |E|`.

The second is the sharper of the two readings below `λ = 1/6` and coincides
with it there, so this loses nothing: the `λ`-free version is this statement
evaluated at a sixth with both sides cleared of denominators.  The depth
conjunct is `deep_depth_le_offset`, which names no constant and is reused as it
stands. -/
theorem exists_deep_orientation_sharp {lam : ℚ} {c t M : List (α × Bool)}
    {j : ℕ}
    (hMsuf : M <:+ palindrome c t)
    (hlow : c.length < M.length)
    (hhigh : M.length ≤ c.length + t.length)
    (hj : (j : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + j) :
    ∃ E : List (α × Bool),
      M = E ++ FreeGroup.invRev c ∧
        FreeGroup.invRev M = c ++ FreeGroup.invRev E ∧
        E <:+ t ∧ (1 - lam) * (t.length : ℚ) < (E.length : ℚ) ∧
        M.length + j - (c.length + t.length) ≤ j := by
  obtain ⟨P', hP'⟩ := hMsuf
  obtain ⟨E, hM, hinvM, hEt, -, -⟩ :=
    eaten_prefix_orientation hP'.symm hlow hhigh
  exact ⟨E, hM, hinvM, hEt, one_sub_lam_mul_lt_eaten hM hj hgt,
    deep_depth_le_offset hM hEt⟩

/-! ## 2.  The back loss, in the backward orientation -/

/-- **The landing factor's own block eats only a `λ`-fraction of its rotation.**
The `λ`-twin of `GreendlingerDeepOverrunCount.six_mul_back_lt_of_backward`.

Same junction, same data, same one-line proof: distinctness comes from
`GreendlingerCoincidence.invRev_ne_rotate_of_minimal`, which reads no constant,
and the piece bound is taken from `intrusion_lt_of_metric` instead of from
`six_mul_intrusion_lt`.  Only two things move — the `C'(1/6)` hypothesis becomes
`C'(λ)`, and the conclusion `6|E₃| < |t₃|` becomes `|E₃| < λ|t₃|`.

The scope of the `λ`-free version is inherited unchanged: `hintr` says the
stretch lands in the next factor's relator territory, which is precisely what
fails at a deep landing factor, so this closes the back side only at a shallow
one. -/
theorem back_lt_of_backward_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {c₃ t₃ c₄ t₄ dw q E₃ : List (α × Bool)}
    {e₁ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c₃, t₃) :: (e₁ ++ ((FreeGroup.mk c₄, t₄) :: f))) g)
    (ht₃ : t₃ ∈ symmetrization R) (ht₄ : t₄ ∈ symmetrization R)
    (hE : E₃ <:+ t₃)
    (hd : FreeGroup.mk dw = conjEval e₁ * FreeGroup.mk c₄)
    (hcq : c₃ = dw ++ q) (hq : q <+: t₄)
    (hintr : FreeGroup.invRev E₃ <+: t₄.rotate q.length) :
    (E₃.length : ℚ) < lam * (t₃.length : ℚ) :=
  (intrusion_lt_of_metric hmetric ht₃ ht₄ hE hintr
    (invRev_ne_rotate_of_minimal hmin hd hcq hq)).1

/-! ## 3.  The back loss, in the overrun orientation

The `λ`-free file projects the head half of the double bound at both
orientations.  Here the overrun orientation is proved once in its full form —
both conjuncts, since they come out of the same call and the second is the
bound against the *next* rotation, which is the shape a sharp landing field
reads — and the twin proper is its first projection. -/

/-- **The double bound at the landing factor's own junction, at any `λ`.**

The full form of `GreendlingerDeepOverrunCount.six_mul_back_lt_of_forward`'s
single `intrusion_lt_of_metric` call, in the orientation where the next
factor's effective conjugator extends the landing factor's own.

The two rotation offsets are matched exactly as in the `λ`-free proof: the
piece bound asks to refute `invRev t₃ = t₄.rotate k`, the forward containment
refutes `t₄ = (invRev t₃).rotate |y|`, and `hindex` — the caller's own
bookkeeping — identifies `|y|` with `|t₄| − k` between them.  Neither
`eq_rotate_invRev_of_invRev_eq_rotate` nor
`ne_rotate_invRev_of_minimal_forward` mentions a constant, so replacing
`six_mul_intrusion_lt` by `intrusion_lt_of_metric` is the whole of the
change. -/
theorem back_lt_both_of_forward_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {c₃ t₃ c₄ t₄ dw y E₃ : List (α × Bool)} {k : ℕ}
    {e₁ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c₃, t₃) :: (e₁ ++ ((FreeGroup.mk c₄, t₄) :: f))) g)
    (ht₃ : t₃ ∈ symmetrization R) (ht₄ : t₄ ∈ symmetrization R)
    (hE : E₃ <:+ t₃)
    (hd : FreeGroup.mk dw = conjEval e₁ * FreeGroup.mk c₄)
    (hcy : dw = c₃ ++ y) (hy : y <+: FreeGroup.invRev t₃)
    (hk : k ≤ t₄.length) (hindex : y.length = t₄.length - k)
    (hintr : FreeGroup.invRev E₃ <+: t₄.rotate k) :
    (E₃.length : ℚ) < lam * (t₃.length : ℚ) ∧
      (E₃.length : ℚ) < lam * (t₄.length : ℚ) := by
  refine intrusion_lt_of_metric hmetric ht₃ ht₄ hE hintr ?_
  intro hcon
  refine ne_rotate_invRev_of_minimal_forward hmin hd hcy hy ?_
  rw [hindex]
  exact eq_rotate_invRev_of_invRev_eq_rotate hk hcon

/-- **The same bound at any `λ`, where the next factor's effective conjugator
extends the landing factor's own.**  The `λ`-twin of
`GreendlingerDeepOverrunCount.six_mul_back_lt_of_forward`.

Every structural hypothesis is quoted verbatim; the `C'(1/6)` hypothesis
becomes `C'(λ)` and the conclusion `6|E₃| < |t₃|` becomes `|E₃| < λ|t₃|`.  The
argument is the first projection of the double bound above.

The scope note of the backward version applies verbatim here as well: `hintr`
fails at a deep landing factor, so this too closes the back side only at a
shallow one. -/
theorem back_lt_of_forward_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {c₃ t₃ c₄ t₄ dw y E₃ : List (α × Bool)} {k : ℕ}
    {e₁ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c₃, t₃) :: (e₁ ++ ((FreeGroup.mk c₄, t₄) :: f))) g)
    (ht₃ : t₃ ∈ symmetrization R) (ht₄ : t₄ ∈ symmetrization R)
    (hE : E₃ <:+ t₃)
    (hd : FreeGroup.mk dw = conjEval e₁ * FreeGroup.mk c₄)
    (hcy : dw = c₃ ++ y) (hy : y <+: FreeGroup.invRev t₃)
    (hk : k ≤ t₄.length) (hindex : y.length = t₄.length - k)
    (hintr : FreeGroup.invRev E₃ <+: t₄.rotate k) :
    (E₃.length : ℚ) < lam * (t₃.length : ℚ) :=
  (back_lt_both_of_forward_sharp hmetric hmin ht₃ ht₄ hE hd hcy hy hk hindex
    hintr).1

end SmallCancellationRouter
end GroupApproximation
