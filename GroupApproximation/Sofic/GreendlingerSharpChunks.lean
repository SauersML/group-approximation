import GroupApproximation.Sofic.GreendlingerChunks
import GroupApproximation.Sofic.GreendlingerSharpRigidity

/-!
# The chunk arithmetic at an arbitrary constant

`GreendlingerChunks` ends with three statements that mention no words at all:
`survivor_le_of_overrun`, `survivor_gt_of_two_pieces` and
`not_consecutive_overrun` are inequalities between natural numbers, each
discharged by `omega`, and `GreendlingerDeepThreeFactor` names all three as what
`DeepOverrunDepth` is to be discharged against.  Being about lengths and nothing
else, they are the cheapest part of the lane to state at an arbitrary `λ`, and
that is what this file does.

## What moves and what does not

Only the piece bounds move.  A hug is bounded by `hug_le_of_minimal_reroute`,
which is a reroute count on the total conjugator length: it says `2q ≤ T`
whatever the small-cancellation constant is, and no twin of it is needed or
possible.  What `C'(λ)` supplies is the other side, `6p < T` at a sixth and
`p < λ·T` in general.

The two conclusions then read `m < (1/2 + λ)·T` and `(1 − 2λ)·T < m`.  At
`λ = 1/6` both constants are `2/3` --- that is `overrun_bounds_meet_at_sixth`
--- which is exactly why the `λ`-free file could afford to state them as
`3m ≤ 2T` and `2T < 3m` and let `omega` collide them.  Below a sixth the two
separate by `(1/2 − 3λ)·T`, so `not_consecutive_overrun_sharp` holds with room
throughout the band the lane runs in.  Above it the collision stops:
`not_consecutive_overrun_sharp_is_tight` exhibits a configuration at `λ = 1/5`
satisfying every hypothesis, so the band is spent for a reason and not out of
caution.

## Abstract lengths

Every variable is rational, as in `GreendlingerSharpTwins` §2, so the
arithmetic can be read on its own.  The nonnegativity that `ℕ` supplies for free
is then taken as a hypothesis, but only in the two statements that actually
consume it.

## The weight bounds

`GreendlingerWeight` carries a hardcoded `2` in `overhang_le_of_minimal`
(`|q| ≤ 2|p|`), but that `2` is a weight *saving* --- swapping the two factors
recovers `|q| − 2|p|` letters --- and not a fraction of a relator, so that file
and its neighbours are `λ`-neutral and have no twins.  The constant enters only
where `GreendlingerRegime` collides those bounds with the piece bound, and §3
states the arithmetic of exactly those collisions: `λ ≤ 1/3` for the slide,
`λ ≤ 1/2` for the meet, both far wider than the sixth the lane spends
elsewhere.

Nothing here is new mathematics; it is the `λ = 1/6` evaluation undone.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The overrun count, at an arbitrary constant -/

/-- **A block that overruns leaves the next factor at most `1/2 + λ`.**  The
sharp twin of `survivor_le_of_overrun`.

To overrun, the block covers the whole surviving stretch `m` of the next
rotation, and it covers it with a hug --- at most half the rotation, by
`GreendlingerThreeFactor.hug_le_of_minimal_reroute`, a bound on the conjugator
weight that does not see `λ` --- followed by a piece, under `λ·T` by `C'(λ)`.
At `λ = 1/6` the conclusion is `m < (2/3)·T`, which is the `λ`-free file's
`3m ≤ 2T`. -/
theorem survivor_le_of_overrun_sharp {lam m q p T : ℚ}
    (hcover : m = q + p) (hhug : 2 * q ≤ T) (hpiece : p < lam * T) :
    m < (1 / 2 + lam) * T := by
  have hexp : (1 / 2 + lam) * T = T / 2 + lam * T := by ring
  rw [hexp]
  linarith

/-- **A block that overruns eats only two pieces**, so its own factor keeps more
than `1 − 2λ` of its rotation.  The sharp twin of `survivor_gt_of_two_pieces`:
past the next factor the block lands among relator letters, so both segments of
the loss `E` are pieces.

This is the two-piece count in the shape the descent produces it --- the loss is
given by an equation, `m + E = T`, and no truncated subtraction appears.
`GreendlingerSharpWindow.sharp_survivor_of_two_pieces` is the same count written
against `T − i − k` in `ℕ`, and lands on the looser `1 − 3λ` that the sharp
conclusion asks for; here the tight `1 − 2λ` is kept, because the collision in
`not_consecutive_overrun_sharp` needs every bit of it. -/
theorem survivor_gt_of_two_pieces_sharp {lam m E p D T : ℚ}
    (hkeep : m + E = T) (hsplit : E = p + D)
    (hp : p < lam * T) (hD : D < lam * T) :
    (1 - 2 * lam) * T < m := by
  have hexp : (1 - 2 * lam) * T = T - 2 * (lam * T) := by ring
  rw [hexp]
  linarith

/-- **Overruns cannot occur at two consecutive levels**, at any `λ ≤ 1/6`.  The
sharp twin of `not_consecutive_overrun`.

One overrun forces the next factor's survivor under `(1/2 + λ)·T`, the other
forces it over `(1 − 2λ)·T`, and the two cross exactly when `3λ ≤ 1/2`.  The
`λ`-free version is the boundary case, where both bounds are `2/3` and the
contradiction comes from the strictness alone; strictly inside the band there is
a margin of `(1/2 − 3λ)·T`. -/
theorem not_consecutive_overrun_sharp {lam m q p E p' D T : ℚ}
    (hlam : lam ≤ 1 / 6) (hT : 0 < T)
    (hcover : m = q + p) (hhug : 2 * q ≤ T) (hpiece : p < lam * T)
    (hkeep : m + E = T) (hsplit : E = p' + D)
    (hp' : p' < lam * T) (hD : D < lam * T) : False := by
  have hle := survivor_le_of_overrun_sharp hcover hhug hpiece
  have hgt := survivor_gt_of_two_pieces_sharp hkeep hsplit hp' hD
  have h6 : lam * T ≤ 1 / 6 * T := mul_le_mul_of_nonneg_right hlam hT.le
  have hexp1 : (1 / 2 + lam) * T = T / 2 + lam * T := by ring
  have hexp2 : (1 - 2 * lam) * T = T - 2 * (lam * T) := by ring
  rw [hexp1] at hle
  rw [hexp2] at hgt
  linarith

/-! ## 2.  Where the band is spent -/

/-- **The two overrun bounds meet at a sixth.**  `1/2 + λ` and `1 − 2λ` are both
`2/3` there, which is why the `λ`-free file states them as `3m ≤ 2T` and
`2T < 3m`: it is reading a single number twice, from opposite sides. -/
theorem overrun_bounds_meet_at_sixth :
    (1 : ℚ) / 2 + 1 / 6 = 2 / 3 ∧ (1 : ℚ) - 2 * (1 / 6) = 2 / 3 := by
  norm_num

/-- **The sixth in `not_consecutive_overrun_sharp` is not decoration.**  At
`λ = 1/5` a rotation of length `10` carries the whole configuration: a survivor
`13/2` covered by a hug of `5` and a piece of `3/2`, whose complement `7/2`
splits into two pieces of `7/4` --- every hypothesis holds and no contradiction
follows.

Machine-checked, in the same spirit as
`GreendlingerSharpTwins.three_pieces_budget_is_tight`: the band cannot be
widened by rearranging the hypotheses, only by changing them. -/
theorem not_consecutive_overrun_sharp_is_tight :
    ¬ ∀ lam m q p E p' D T : ℚ, 0 < T → m = q + p → 2 * q ≤ T →
      p < lam * T → m + E = T → E = p' + D → p' < lam * T → D < lam * T →
      False := by
  intro h
  exact h (1 / 5) (13 / 2) 5 (3 / 2) (7 / 2) (7 / 4) (7 / 4) 10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-! ## 3.  The minimality bounds, read against a general constant -/

/-- **A long overhang and a short overlap still exclude each other**, for every
`λ ≤ 1/3`.

`GreendlingerWeight.overhang_le_of_minimal` gives `q ≤ 2p` from the weight of
the slide move, and `C'(λ)` bounds the overlap `p` against the rotation `q ++ p`
it prefixes.  Together `p < λ·(q + p) ≤ 3λ·p ≤ p`.  `GreendlingerRegime` runs
this collision at a sixth, where it closes by `omega` because `6p < q + p` reads
`5p < q`; the fraction it actually needs is a third. -/
theorem not_overhang_of_slide_sharp {lam p q : ℚ} (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ 1 / 3) (hp0 : 0 ≤ p)
    (hpiece : p < lam * (q + p)) (hover : q ≤ 2 * p) : False := by
  have h1 : lam * (q + p) ≤ lam * (3 * p) :=
    mul_le_mul_of_nonneg_left (by linarith) hlam0
  have h2 : lam * (3 * p) ≤ 1 / 3 * (3 * p) :=
    mul_le_mul_of_nonneg_right hlam (by linarith)
  linarith

/-- **The meet bound and the piece bound exclude each other**, for every
`λ ≤ 1/2`.

`GreendlingerWeight.overhang_le_of_minimal_meet` gives `y ≤ v` where `y` is the
overhang and `v` the stretch the two rotations share, and the inverted head
rotation is `y ++ v`, so `T = y + v ≤ 2v`; the piece bound on `v` against that
rotation then reads `v < λ·T ≤ 2λ·v ≤ v`.  Half is all this collision costs,
so it is nowhere near the constraint on the band. -/
theorem not_overhang_of_meet_sharp {lam v y T : ℚ} (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ 1 / 2) (hv0 : 0 ≤ v) (hsum : y + v = T)
    (hover : y ≤ v) (hpiece : v < lam * T) : False := by
  have h1 : lam * T ≤ lam * (2 * v) :=
    mul_le_mul_of_nonneg_left (by linarith) hlam0
  have h2 : lam * (2 * v) ≤ 1 / 2 * (2 * v) :=
    mul_le_mul_of_nonneg_right hlam (by linarith)
  linarith

/-- **A symmetrized relator is not a piece of itself**, at any `λ ≤ 1`.

The degenerate branch of the regime split, where one rotation covers another
whole: the metric condition applied to `w` as a prefix of itself gives
`|w| < λ·|w| ≤ |w|`.  At a sixth this is `6|w| < |w|`, which the `λ`-free
argument closes by `omega` against a separately proved `w ≠ []`.  Here no
nonemptiness is needed --- at `w = []` the bound reads `0 < 0` --- so this also
subsumes the empty case that `GreendlingerSharpTwins.ne_nil_of_metric_lam`
reaches through the empty piece. -/
theorem not_isPiece_self_sharp {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1) (hmetric : MetricSmallCancellation R lam)
    {w : List (α × Bool)} (hw : w ∈ symmetrization R)
    (hpiece : IsPiece (symmetrization R) w) : False := by
  have h := hmetric w hpiece w hw (List.prefix_refl w)
  have hle : lam * (w.length : ℚ) ≤ 1 * (w.length : ℚ) :=
    mul_le_mul_of_nonneg_right hlam (Nat.cast_nonneg _)
  linarith

end SmallCancellationRouter
end GroupApproximation
