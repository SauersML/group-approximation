import GroupApproximation.Sofic.GreendlingerSharpRigidity
import GroupApproximation.Sofic.GreendlingerDeepInduction

/-!
# The three-factor overrun at an arbitrary constant

`GreendlingerDeepThreeFactor` settles the shape of the three-factor overrun and
reduces it to one inequality, `2(i + d) < |t₃|`, isolated as `DeepOverrunDepth`.
`GreendlingerDeepInduction` then frames that count: `DeepOverrunDepth` together
with `DeepOverrunLandingTail` gives `DeepOverrunLanding`, and the frame
`deepOverrunArc_of_landing` turns it into `DeepOverrunArc`.

Half of that chain is already twinned.  `greendlingerAtSharp_of_landing_intrusion`
is the sharp arc producer at the rotation, `deepOverrunArcSharp_of_landingSharp`
is the sharp frame, and `cast_add_lt_three_mul_of_relator_ratio` is the sharp
arithmetic.  What was missing is the middle: the producers that read the arc off
a **drop of the whole palindrome** rather than off the rotation, and the count
predicate they consume.  This file supplies exactly that, statement for
statement, so that the sharp lane has the same route to `DeepOverrunArcSharp`
that the `λ`-free lane has to `DeepOverrunArc`:

```
DeepOverrunDepthSharp + DeepOverrunLandingTailSharp
  → DeepOverrunLandingSharp     (deepOverrunLandingSharp_of_depthSharp_of_tailSharp)
  → DeepOverrunArcSharp         (deepOverrunArcSharp_of_landingSharp, existing)
```

Nothing here discharges either family; the file is a reduction, in the same
sense `GreendlingerSharpReduction` is one along the window route.  The two
routes are alternatives, not competitors: this one keeps the three-factor count
as the deep obligation, the window one replaces it.

## The `3λ` budget, and where `λ ≤ 1/3` is read

The sharp conclusion asks for an arc longer than `(1 − 3λ)` of its rotation, so
its whole allowance is `3λ|t₃|`, and in the overrun the intrusion `i` and the
overrun depth `d` are the two claims on it — which is
`GreendlingerSharpTwins.three_pieces_budget`'s right-hand side.  At `λ = 1/6`
the budget reads `2(i + d) < |t₃|`, which is the `λ`-free inequality.

Every producer below therefore takes the budget hypothesis
`(i : ℚ) + (d : ℚ) < 3λ|t₃|` and nothing else about the constant — except for
the list-theoretic fit `i + d ≤ |t₃|`, which the `λ`-free lane got from `omega`
inside the same `2(i + d) < |t₃|` and which here has to be produced.
`add_le_length_of_three_lam_budget` produces it from `λ ≤ 1/3`, that being the
exact point at which the budget is at most the whole rotation.  The sharp lane
runs at `λ ≤ 1/6`, so callers there discharge it by `linarith`; it is stated at
`1/3` because that is what the arithmetic actually uses.

## What is quoted and what is proved

The two branch structures — a drop that reaches past the landing conjugator and
one that stops inside it — are quoted from `greendlingerAt_of_landing_drop` and
`greendlingerAt_of_landing_start` line for line, with `omega` replaced by the
rational bookkeeping and `GreendlingerAt` by `GreendlingerAtSharp`.  The
`ℕ`-subtraction `N − |c₃|` collapses to `0` on the second branch, which at
`λ = 1/6` was invisible inside `omega` and here is the rewrite `hz`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The fit the `λ`-free lane got for free -/

/-- **The `3λ` budget bounds the rotation's own length.**  A budget of `3λ|t₃|`
is at most `|t₃|` as soon as `λ ≤ 1/3`, so anything strictly inside the budget
fits inside the rotation.

This is the one piece of arithmetic the `λ`-free lane never had to state: there
the budget is `2(i + d) < |t₃|`, which already *is* the fit, and `omega` reads
both off the same inequality.  Stated rationally the two come apart, and every
arc producer below needs the fit to know that its `take` does not saturate. -/
theorem add_le_length_of_three_lam_budget {lam : ℚ} {t₃ : List (α × Bool)}
    {i d : ℕ} (hlam : lam ≤ 1 / 3)
    (hbound : (i : ℚ) + (d : ℚ) < 3 * lam * (t₃.length : ℚ)) :
    i + d ≤ t₃.length := by
  have hT : (0 : ℚ) ≤ (t₃.length : ℚ) := by positivity
  have hcoef : 3 * lam ≤ 1 := by linarith
  have hle : 3 * lam * (t₃.length : ℚ) ≤ 1 * (t₃.length : ℚ) :=
    mul_le_mul_of_nonneg_right hcoef hT
  have hq : ((i + d : ℕ) : ℚ) < (t₃.length : ℚ) := by
    rw [Nat.cast_add]
    linarith
  exact_mod_cast hq.le

/-! ## 2.  The landing arc, read off a drop of the palindrome -/

/-- **The sharp landing arc, from a drop of the whole palindrome.**  The
`λ`-twin of `GreendlingerDeepThreeFactor.greendlingerAt_of_landing_drop`: the
surviving word is the last palindrome with `N` letters removed, the intrusion
into its rotation is `N − |c₃|`, and the budget is claimed by that intrusion
together with the offset `d`.

Both regimes are covered exactly as in the `λ`-free version.  When the block
reaches past the last conjugator the drop lands inside the rotation and the arc
is `greendlingerAtSharp_of_landing_intrusion` directly; when it stops inside the
conjugator the intrusion is `0`, the surviving conjugator letters are prepended,
and the located offset only improves. -/
theorem greendlingerAtSharp_of_landing_drop {R : Set (List (α × Bool))}
    {lam : ℚ} {c₃ t₃ : List (α × Bool)} {N d : ℕ}
    (ht₃ : t₃ ∈ symmetrization R)
    (hfit : (N - c₃.length) + d ≤ t₃.length)
    (hbound : ((N - c₃.length : ℕ) : ℚ) + (d : ℚ)
      < 3 * lam * (t₃.length : ℚ)) :
    GreendlingerAtSharp R lam d ((palindrome c₃ t₃).drop N) := by
  have hP : palindrome c₃ t₃ = c₃ ++ (t₃ ++ FreeGroup.invRev c₃) := by
    unfold palindrome
    rw [List.append_assoc]
  rcases le_or_gt c₃.length N with hle | hgt
  · have hdrop : (palindrome c₃ t₃).drop N
        = (t₃ ++ FreeGroup.invRev c₃).drop (N - c₃.length) := by
      rw [hP, drop_append_of_ge c₃ N _ hle]
    rw [hdrop]
    exact greendlingerAtSharp_of_landing_intrusion ht₃ hfit hbound
  · have hz : N - c₃.length = 0 := by omega
    rw [hz] at hfit hbound
    have hdrop : (palindrome c₃ t₃).drop N
        = c₃.drop N ++ (t₃ ++ FreeGroup.invRev c₃).drop 0 := by
      rw [hP, drop_append_of_le N c₃ _ hgt.le, List.drop_zero]
    rw [hdrop]
    refine ((greendlingerAtSharp_of_landing_intrusion (i := 0) (d := d) ht₃
      hfit hbound).append_left (c₃.drop N)).mono ?_
    omega

/-- **The count, split in two, at the sharp constant.**  The `λ`-twin of
`GreendlingerDeepThreeFactor.greendlingerAt_of_piece_intrusion`, and the split
that file names: the intrusion is a piece, so it costs `λ|t₃|`, and the overrun
depth is allowed the remaining `2λ|t₃|`.  Their sum is the whole `3λ`
allowance, which is why the split is exact rather than generous.

At `λ = 1/6` the two halves read `6(N − |c₃|) < |t₃|` and `3d < |t₃|`. -/
theorem greendlingerAtSharp_of_piece_intrusion {R : Set (List (α × Bool))}
    {lam : ℚ} {c₃ t₃ : List (α × Bool)} {N d : ℕ}
    (hlam : lam ≤ 1 / 3)
    (ht₃ : t₃ ∈ symmetrization R)
    (hi : ((N - c₃.length : ℕ) : ℚ) < lam * (t₃.length : ℚ))
    (hd : (d : ℚ) < 2 * lam * (t₃.length : ℚ)) :
    GreendlingerAtSharp R lam d ((palindrome c₃ t₃).drop N) := by
  have hbound : ((N - c₃.length : ℕ) : ℚ) + (d : ℚ)
      < 3 * lam * (t₃.length : ℚ) := by linarith
  exact greendlingerAtSharp_of_landing_drop ht₃
    (add_le_length_of_three_lam_budget hlam hbound) hbound

/-! ## 3.  The arc at the start of the survivor -/

/-- **The sharp arc at the start of the survivor.**  The `λ`-twin of
`GreendlingerDeepThreeFactor.greendlingerAt_of_landing_start`: read at the
position where the landing rotation's surviving stretch begins — `|c₃| − N`,
which is `0` once the block has reached into the rotation — the arc claims no
part of the budget for the offset, so the whole `3λ|t₃|` is left to the
intrusion.

The `λ`-free version measures this as `2(N − |c₃|) < |t₃|`, the `d = 0` case of
its count; this is the `d = 0` case of the budget, and the `0` has to be carried
through the cast, which is what `hbound` does. -/
theorem greendlingerAtSharp_of_landing_start {R : Set (List (α × Bool))}
    {lam : ℚ} {c₃ t₃ : List (α × Bool)} {N : ℕ}
    (hlam : lam ≤ 1 / 3)
    (ht₃ : t₃ ∈ symmetrization R)
    (hi : ((N - c₃.length : ℕ) : ℚ) < 3 * lam * (t₃.length : ℚ)) :
    GreendlingerAtSharp R lam (c₃.length - N) ((palindrome c₃ t₃).drop N) := by
  have hbound : ((N - c₃.length : ℕ) : ℚ) + ((0 : ℕ) : ℚ)
      < 3 * lam * (t₃.length : ℚ) := by
    rw [Nat.cast_zero, add_zero]
    exact hi
  have hfit : (N - c₃.length) + 0 ≤ t₃.length :=
    add_le_length_of_three_lam_budget hlam hbound
  have hP : palindrome c₃ t₃ = c₃ ++ (t₃ ++ FreeGroup.invRev c₃) := by
    unfold palindrome
    rw [List.append_assoc]
  rcases le_or_gt c₃.length N with hle | hgt
  · have hz : c₃.length - N = 0 := by omega
    rw [hz]
    exact greendlingerAtSharp_of_landing_drop (d := 0) ht₃ hfit hbound
  · have hz : N - c₃.length = 0 := by omega
    rw [hz] at hfit hbound
    have hdrop : (palindrome c₃ t₃).drop N
        = c₃.drop N ++ (t₃ ++ FreeGroup.invRev c₃).drop 0 := by
      rw [hP, drop_append_of_le N c₃ _ hgt.le, List.drop_zero]
    rw [hdrop]
    refine ((greendlingerAtSharp_of_landing_intrusion (i := 0) (d := 0) ht₃
      hfit hbound).append_left (c₃.drop N)).mono ?_
    rw [List.length_drop]
    omega

/-- **... and the piece bound alone pays for it.**  The `λ`-twin of
`GreendlingerDeepThreeFactor.greendlingerAt_of_landing_start_of_piece`: an
intrusion under `λ|t₃|` is under `3λ|t₃|` as soon as `λ ≥ 0`, so the weakened
conclusion needs nothing beyond what `C'(λ)` already gives — no ratio between
the two rotations and no bound on the overrun depth.

`0 ≤ λ` is what replaces the `λ`-free version's "a sixth is under a half": at a
negative constant the budget would run the other way. -/
theorem greendlingerAtSharp_of_landing_start_of_piece
    {R : Set (List (α × Bool))} {lam : ℚ} {c₃ t₃ : List (α × Bool)} {N : ℕ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 3)
    (ht₃ : t₃ ∈ symmetrization R)
    (hpiece : ((N - c₃.length : ℕ) : ℚ) < lam * (t₃.length : ℚ)) :
    GreendlingerAtSharp R lam (c₃.length - N) ((palindrome c₃ t₃).drop N) := by
  refine greendlingerAtSharp_of_landing_start hlam ht₃ ?_
  have hT : (0 : ℚ) ≤ (t₃.length : ℚ) := by positivity
  have hml : (0 : ℚ) ≤ lam * (t₃.length : ℚ) := mul_nonneg hlam0 hT
  linarith

/-! ## 4.  The ratio producer, in the palindrome-drop form -/

/-- **The sharp landing arc, closed by the balanced-family ratio, read off the
palindrome.**  The `λ`-twin of
`GreendlingerDeepOverrunCount.greendlingerAt_of_landing_ratio`.

`greendlingerAtSharp_of_landing_ratio` already proves the same thing against the
rotation, `(t₃ ++ Z).drop (N − |c₃|)`; this is the form the three-factor
decomposition actually produces, where the surviving word is the whole last
palindrome with `N` letters removed and the block may still be inside the last
conjugator.  The arithmetic is unchanged —
`cast_add_lt_three_mul_of_relator_ratio` supplies the budget from the piece
bound, the offset bound and `|t| ≤ 2|t₃|` — and only the branch on where the
drop lands is added. -/
theorem greendlingerAtSharp_of_landing_ratio_drop {R : Set (List (α × Bool))}
    {lam : ℚ} {c t c₃ t₃ M E : List (α × Bool)} {N j : ℕ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 3)
    (ht₃ : t₃ ∈ symmetrization R)
    (hM : M = E ++ FreeGroup.invRev c) (hEt : E <:+ t)
    (hj : (j : ℚ) < lam * (t.length : ℚ))
    (hpiece : ((N - c₃.length : ℕ) : ℚ) < lam * (t₃.length : ℚ))
    (hratio : t.length ≤ 2 * t₃.length) :
    GreendlingerAtSharp R lam (M.length + j - (c.length + t.length))
      ((palindrome c₃ t₃).drop N) := by
  have hd : M.length + j - (c.length + t.length) ≤ j :=
    deep_depth_le_offset (j := j) hM hEt
  have hbound : ((N - c₃.length : ℕ) : ℚ)
      + ((M.length + j - (c.length + t.length) : ℕ) : ℚ)
      < 3 * lam * (t₃.length : ℚ) :=
    cast_add_lt_three_mul_of_relator_ratio hpiece hj hd hlam0 hratio
  exact greendlingerAtSharp_of_landing_drop ht₃
    (add_le_length_of_three_lam_budget hlam hbound) hbound

/-! ## 5.  The three-factor count, isolated at the sharp constant -/

/-- **The `λ`-twin of `GreendlingerDeepThreeFactor.DeepOverrunDepth`.**

Every structural field is quoted verbatim; the two that carry the constant move.
The offset hypothesis becomes `j < λ|t|`, and the conclusion becomes the budget
inequality — the intrusion into the last rotation plus the depth by which the
head's block overran its own palindrome, together strictly inside `3λ|t₃|`.

At `λ = 1/6` the conclusion is the `λ`-free `2(i + d) < |t₃|` with the
denominator cleared, which is the sense in which the constant was never in the
count: it entered only when `GreendlingerPiece.six_mul_length_lt_of_isPiece`
cleared it once so that the whole configuration could be discharged in `ℕ`.

What should discharge it is the sharp Chunks arithmetic:
`GreendlingerSharpChunks.survivor_le_of_overrun_sharp` caps the second factor's
survivor at `(1/2 + λ)|t₂|` when the block overruns it,
`survivor_gt_of_two_pieces_sharp` pushes the other way at `(1 − 2λ)|t₂|`, and
`not_consecutive_overrun_sharp` is the two together.  Those are stated over
abstract rationals, so feeding them here is a matter of naming the segments the
count runs over, not of new geometry — the same remark the `λ`-free file makes
about its own `ℕ`-valued versions. -/
def DeepOverrunDepthSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t c₂ t₂ c₃ t₃ M B' : List (α × Bool)) (g : FreeGroup α) (j N : ℕ),
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂)
        :: [(FreeGroup.mk c₃, t₃)]) g →
    t ∈ symmetrization R → t₂ ∈ symmetrization R → t₃ ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c₂ t₂) →
    FreeGroup.IsReduced (palindrome c₃ t₃) →
    M <:+ palindrome c t →
    (conjEval ((FreeGroup.mk c₂, t₂)
      :: [(FreeGroup.mk c₃, t₃)])).toWord = FreeGroup.invRev M ++ B' →
    ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂) →
    B' = (palindrome c₃ t₃).drop N →
    c.length < M.length → (j : ℚ) < lam * (t.length : ℚ) →
    c.length + t.length < M.length + j →
    ((N - c₃.length : ℕ) : ℚ)
      + ((M.length + j - (c.length + t.length) : ℕ) : ℚ)
      < 3 * lam * (t₃.length : ℚ)

/-- **The three-factor overrun case, from the sharp count.**  The `λ`-twin of
`GreendlingerDeepThreeFactor.greendlingerAt_of_deepOverrunDepth`, and the same
two steps: the decomposition `exists_three_factor_landing_drop` is `λ`-free and
is reused as it stands, and the producer is the sharp landing-drop arc.

`DeepOverrunDepthSharp` is the whole of what is assumed; `λ ≤ 1/3` buys only the
fit. -/
theorem greendlingerAtSharp_of_deepOverrunDepthSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 3)
    (h : DeepOverrunDepthSharp R lam)
    {c t c₂ t₂ c₃ t₃ M B' : List (α × Bool)} {g : FreeGroup α} {j : ℕ}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂)
        :: [(FreeGroup.mk c₃, t₃)]) g)
    (ht : t ∈ symmetrization R) (ht₂ : t₂ ∈ symmetrization R)
    (ht₃ : t₃ ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (hredp₃ : FreeGroup.IsReduced (palindrome c₃ t₃))
    (hMsuf : M <:+ palindrome c t)
    (htail : (conjEval ((FreeGroup.mk c₂, t₂)
      :: [(FreeGroup.mk c₃, t₃)])).toWord = FreeGroup.invRev M ++ B')
    (hover : ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂))
    (hlow : c.length < M.length) (hj : (j : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + j) :
    GreendlingerAtSharp R lam (M.length + j - (c.length + t.length)) B' := by
  obtain ⟨N, hB'⟩ :=
    exists_three_factor_landing_drop hredp₂ hredp₃ htail hover
  have hbound := h c t c₂ t₂ c₃ t₃ M B' g j N hmin ht ht₂ ht₃ hredp hredp₂
    hredp₃ hMsuf htail hover hB' hlow hj hgt
  rw [hB']
  exact greendlingerAtSharp_of_landing_drop ht₃
    (add_le_length_of_three_lam_budget hlam hbound) hbound

/-! ## 6.  The landing chain, at the sharp constant -/

/-- **The `λ`-twin of `GreendlingerDeepInduction.DeepOverrunLandingTail`.**
`DeepOverrunLandingSharp` restricted to expressions with a fourth factor, which
is what is left once the three-factor count is spent: `DeepOverrunDepthSharp`
reads the last factor's word as its own palindrome and so is stated at exactly
three factors.

Only the offset hypothesis and the arc bound move; the fourth factor is left as
it stands rather than in normal form, exactly as in the `λ`-free predicate. -/
def DeepOverrunLandingTailSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t c₂ t₂ c₃ t₃ M B' : List (α × Bool))
    (x : FreeGroup α × List (α × Bool))
    (f : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α) (j N : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂)
      :: (FreeGroup.mk c₃, t₃) :: x :: f) g →
    t ∈ symmetrization R → t₂ ∈ symmetrization R → t₃ ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c₂ t₂) →
    FreeGroup.IsReduced (palindrome c₃ t₃) →
    M <:+ palindrome c t →
    (conjEval ((FreeGroup.mk c₂, t₂)
      :: (FreeGroup.mk c₃, t₃) :: x :: f)).toWord = FreeGroup.invRev M ++ B' →
    ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂) →
    B' = (conjEval ((FreeGroup.mk c₃, t₃) :: x :: f)).toWord.drop N →
    c.length < M.length → (j : ℚ) < lam * (t.length : ℚ) →
    c.length + t.length < M.length + j →
    GreendlingerAtSharp R lam (M.length + j - (c.length + t.length)) B'

/-- **The sharp landing obligation, from the sharp count and the rest.**  The
`λ`-twin of `GreendlingerDeepInduction.deepOverrunLanding_of_depth_of_tail`, and
the same case split on the tail: when the landing factor is the last one the
count applies, and when it is not the residual does.

The supplied drop `hB'` is not read on the first branch — the seed derives its
own from `exists_three_factor_landing_drop`. -/
theorem deepOverrunLandingSharp_of_depthSharp_of_tailSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 3)
    (hdepth : DeepOverrunDepthSharp R lam)
    (htail : DeepOverrunLandingTailSharp R lam) :
    DeepOverrunLandingSharp R lam := by
  intro c t c₂ t₂ c₃ t₃ M B' f g j N hmin ht ht₂ ht₃ hredp hredp₂ hredp₃ hMsuf
    hword hover hB' hlow hj hgt
  cases f with
  | nil =>
      exact greendlingerAtSharp_of_deepOverrunDepthSharp hlam hdepth hmin ht ht₂
        ht₃ hredp hredp₂ hredp₃ hMsuf hword hover hlow hj hgt
  | cons x f' =>
      exact htail c t c₂ t₂ c₃ t₃ M B' x f' g j N hmin ht ht₂ ht₃ hredp hredp₂
        hredp₃ hMsuf hword hover hB' hlow hj hgt

/-- **`DeepOverrunArcSharp` over the sharp count and the one residual.**  The
`λ`-twin of `GreendlingerDeepInduction.deepOverrunArc_of_depth_of_tail`: the
sharp deep regime costs exactly two statements, the three-factor count and the
configuration in which the block lands in a factor that is not the last.

The frame `deepOverrunArcSharp_of_landingSharp` is already twinned and reads
neither the offset hypothesis nor the arc bound. -/
theorem deepOverrunArcSharp_of_depthSharp_of_tailSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 3)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hdepth : DeepOverrunDepthSharp R lam)
    (htail : DeepOverrunLandingTailSharp R lam) :
    DeepOverrunArcSharp R lam :=
  deepOverrunArcSharp_of_landingSharp hR hRne
    (deepOverrunLandingSharp_of_depthSharp_of_tailSharp hlam hdepth htail)

/-- **`CascadeLandingSharp` over the sharp count, the residual and (β).**  The
deep half is the pair above; the other half is the (β) landing production, which
is where `GreendlingerDeepVacuitySharp` leaves the sharp gate.

`λ ≤ 1/6` is the lane's own constraint, read here by the junction kill through
`six_mul_lt_of_lam_lt`; the `λ ≤ 1/3` the count needs follows from it. -/
theorem cascadeLandingSharp_of_depthSharp_of_tailSharp_of_betaSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R lam)
    (hdepth : DeepOverrunDepthSharp R lam)
    (htail : DeepOverrunLandingTailSharp R lam)
    (hbeta : LandingProductionBetaSharp R lam) :
    CascadeLandingSharp R lam :=
  cascadeLandingSharp_of_deepOverrunArcSharp_of_betaSharp hlam hR hRne hmetric
    (deepOverrunArcSharp_of_depthSharp_of_tailSharp (by linarith) hR hRne
      hdepth htail) hbeta

/-! ## 7.  The two-factor vacuity, read at the sharp constant -/

/-- **No two-factor expression is ever deep, at the sharp constant.**  The
`λ`-twin of `GreendlingerDeepVacuity.not_deep_two_factor`.

There is no bound to sharpen: the conclusion is `False`, and the sharp offset
hypothesis is *stronger* than the half-form one below `1/6`, so the single
argument serves both.  The two brackets of `GreendlingerDeepVacuitySharp` are
what pass between them — `six_mul_lt_of_lam_lt` on the offset and
`metricSmallCancellation_of_le` on the constant.

This is the seed the three-factor count sits above: with a single factor in the
tail the destroyed prefix has nowhere to go but the adjacent palindrome, so the
junction kill is the whole story and no overrun arises. -/
theorem not_deep_two_factor_sharp [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R lam)
    {c t c' t' P' M B' : List (α × Bool)} {g : FreeGroup α} {j : ℕ}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: [(FreeGroup.mk c', t')]) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (heq : palindrome c t = P' ++ M)
    (heq' : palindrome c' t' = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) (hj : (j : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + j) : False :=
  not_deep_two_factor hRne (metricSmallCancellation_of_le hlam hmetric) hmin ht
    ht' hredp hredp' heq heq' hlow (six_mul_lt_of_lam_lt hlam hj) hgt

end SmallCancellationRouter
end GroupApproximation
