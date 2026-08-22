import GroupApproximation.Sofic.GreendlingerAlphaPlumb
import GroupApproximation.Sofic.GreendlingerMaxConjugator
import GroupApproximation.Sofic.GreendlingerFreeGate

/-!
# The sharp-form layer: `λ`-parameterized twins of the arithmetic and of the
cascade conclusion

Every route to the gate that the repository walks produces the **half form**:
`GreendlingerAt` stores `|r| < 2·|u|`, `greendlingerConclusion_of_cascadeLanding`
returns `GreendlingerConclusion`, and both are pinned to the constant `1/6`
through the cleared-denominator inequality `6·|piece| < |r|`.

The two statements that consume the gate do not want that form.
`GreendlingerFreeGate.SharpGreendlingerGate` asks for
`GreendlingerConclusionSharp R lam` --- arc bound `(1 − 3λ)·|r|` --- and
`TorsionDescent.isPowerTorsionFree_of_sharp` spends exactly the strength that
form has over the half form: `TorsionDescent.half_form_residual_satisfiable`
exhibits a configuration satisfying every half-form constraint, and
`TorsionDescent.half_form_witness_dies_at_eighth` records that it is the *sharp*
conjunct which kills it.  Half form at `C'(1/8)` gives only `n > (3/8)·|r|`,
which does not empty the torsion residual; nothing in the tree produced the
sharp form, so a closed `CascadeLanding` left `SharpGreendlingerGate` open.

This file supplies the missing form.

## What is duplicated and what is not

The split is the one the design note calls for.

* **Arithmetic is twinned.**  `GreendlingerMaxConjugator`'s inequalities are
  `1/6`-specific by construction: they clear the denominator so that `omega` can
  finish.  Their `λ`-twins live in `ℚ` (§2), because `MetricSmallCancellation`
  states the piece bound in `ℚ` and there is no denominator left to clear.
* **Structure is not twinned.**  Transport, inheritance and the chunk
  decomposition never look at the arc bound: they carry the pair `(s, u)`
  untouched and move only the surrounding decomposition.  So they are restated
  once, at the level of the decomposition alone (`LocatedSplit`, §4), and both
  the half form and the sharp form read that one proof.  `LocatedSplit` is the
  honest statement of what those moves prove; the half-form theorems in
  `GreendlingerThreeFactor` and `GreendlingerCascade` are that statement with a
  particular bound attached, and §4 records both directions of the bridge so the
  claim is checkable rather than asserted.
* **Everything else is consumed unchanged**: `exists_leading_cancellation`,
  `exists_split_take_of_bounded_cancellation`, `take_add_split`,
  `rotate_mem_symmetrization`, `exists_palindromic_head`, `mem_normalClosure_iff`
  and the minimality layer are all `λ`-free.
  `GreendlingerMaxConjugator.not_overrun_into_conjugator` is `λ`-free too --- it
  names no constant, only `T ≤ g + h + p`, `2h + p ≤ T` and `g < h` --- so it
  gets no twin and is cited as it stands.

## Why `1 − 3λ` and not `1 − 2λ`

`three_pieces_budget` is the reason, and `three_pieces_budget_is_tight` is the
proof that it is the reason: three losses each *strictly* under `λ·T` sum to
strictly under `3λ·T`, and with the piece bounds relaxed to `≤` the sum reaches
`3λ·T` exactly.  So `(1 − 3λ)` is the exact budget of the three-piece
configuration --- the maximiser's two junctions plus the offset the descent
spends --- and the two-piece configuration (`two_pieces_budget`) clears it with
a whole `λ·T` to spare.  At `λ = 1/6` the coefficient is `1/2` and the half form
is this one read at a single value; below `1/6` it is strictly stronger, which
is the strength the torsion descent needs.

## The end state

`sharpGreendlingerGate_of_cascadeLandingSharp` produces
`GreendlingerFreeGate.SharpGreendlingerGate α` from one named hypothesis and
nothing else, and `torsionFree_of_cascadeLandingSharp` and
`router_conclusions_of_cascadeLandingSharp` compose it into the torsion and
router layers, so the composition is exhibited rather than asserted.

Everything that is not the residual is proved.  `0 < lam` and
`∀ r ∈ R, r ≠ []` come from the metric condition through the empty piece
(`lam_pos_of_metric`, `ne_nil_of_metric_lam`), the two distinct symmetrized
relators those need come from
`exists_two_distinct_symmetrization` --- a relator and its formal inverse, kept
apart by `invRev_ne_self_of_isCyclicallyReduced` --- and the degenerate family
whose relators are all empty is discharged against the trivial normal closure.
So the gate carries no side conditions, only the residual itself.

§9 carries that end state down to the residuals the lane is actually proving.
`Sofic.GreendlingerAlphaPlumb` discharges case (α) against the descent's own
context and leaves `DeepArcSource` and `LandingProductionBeta`; its `λ`-twins
are `DeepArcSourceSharp` and `LandingProductionBetaSharp`, and
`sharpGreendlingerGate_of_deepArcSharp_of_betaSharp` is the gate over exactly
those two.  The `α` plumbing itself is `λ`-free --- `ConjugatorAbsorbedSite`,
`exists_cascade_split`, `eaten_prefix_orientation` and
`invRev_ne_rotate_of_minimal` name no constant --- so §9 twins only the double
piece bound `six_mul_intrusion_lt` and the three predicates that quote it.

Unconditional except where `DeepArcSourceSharp` and `LandingProductionBetaSharp`
(equivalently `CascadeLandingSharp`) are named.  There is no other hypothesis.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The metric condition at a general constant

`GreendlingerPiece.six_mul_length_lt_of_isPiece` clears the denominator and
lands in `ℕ`; at a general `λ` there is nothing to clear, so these stay in `ℚ`.
-/

/-- **The piece bound on an eaten suffix, at a general constant.**  The `λ`-twin
of `GreendlingerPiece.six_mul_length_lt_of_eaten`: what a cancellation eats off
the end of a rotation has its formal inverse a prefix of a symmetrized relator,
so the metric condition applies to it directly. -/
theorem length_lt_of_eaten {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam) {M t : List (α × Bool)}
    (ht : t ∈ symmetrization R) (hsuf : M <:+ t)
    (hpiece : IsPiece (symmetrization R) (FreeGroup.invRev M)) :
    (M.length : ℚ) < lam * (t.length : ℚ) := by
  have h := hmetric (FreeGroup.invRev M) hpiece (FreeGroup.invRev t)
    (invRev_mem_symmetrization ht) (invRev_prefix_of_suffix hsuf)
  rwa [FreeGroup.invRev_length, FreeGroup.invRev_length] at h

/-- **An empty relator is forbidden, at a general constant.**  The `λ`-twin of
`ne_nil_of_metricSmallCancellation`: as soon as the symmetrization has two
distinct members the empty word is a piece, and a piece is strictly shorter than
`λ` times every relator it prefixes --- which the empty relator is not, whatever
`λ` is. -/
theorem ne_nil_of_metric_lam {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {s₁ s₂ : List (α × Bool)} (hs₁ : s₁ ∈ symmetrization R)
    (hs₂ : s₂ ∈ symmetrization R) (hne : s₁ ≠ s₂)
    {r : List (α × Bool)} (hr : r ∈ symmetrization R) : r ≠ [] := by
  intro hnil
  have hpiece : IsPiece (symmetrization R) [] :=
    ⟨s₁, hs₁, s₂, hs₂, hne, List.nil_prefix, List.nil_prefix⟩
  have h := hmetric [] hpiece r hr List.nil_prefix
  rw [hnil] at h
  simp at h

/-- **The constant is positive on any nondegenerate family.**  The same empty
piece, read against a *nonempty* relator: `0 < λ·|r|`, so `λ > 0`.

This is not decoration.  The sharp conclusion asks for an arc longer than
`(1 − 3λ)·|r|`, and at `λ ≤ 0` that demands an arc longer than the relator it
is a prefix of, which no word supplies.  So `0 < λ` is exactly the hypothesis
under which the sharp form is attainable at all, and the metric condition
supplies it wherever there is anything to prove. -/
theorem lam_pos_of_metric {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {s₁ s₂ : List (α × Bool)} (hs₁ : s₁ ∈ symmetrization R)
    (hs₂ : s₂ ∈ symmetrization R) (hne : s₁ ≠ s₂)
    {r : List (α × Bool)} (hr : r ∈ symmetrization R) (hrne : r ≠ []) :
    0 < lam := by
  have hpiece : IsPiece (symmetrization R) [] :=
    ⟨s₁, hs₁, s₂, hs₂, hne, List.nil_prefix, List.nil_prefix⟩
  have h := hmetric [] hpiece r hr List.nil_prefix
  rw [List.length_nil, Nat.cast_zero] at h
  have hrpos : (0 : ℚ) < (r.length : ℚ) := by
    have hpos : 0 < r.length := List.length_pos_iff.mpr hrne
    exact_mod_cast hpos
  by_contra hcon
  push Not at hcon
  nlinarith

/-- **A nonempty cyclically reduced word is not its own formal inverse.**

The head letter and the last letter decide it.  `getLast?_invRev` says the last
letter of `invRev r` is the inversion of `r`'s *first* letter, so if `invRev r`
were `r` then `r`'s last letter would be `invLetter b` where `b` is its first.
Cyclic reduction is exactly the reduction step read across the seam --- by
`isReduced_step_iff` it says the first letter is not the inversion of the last
--- and here the last is `invLetter b`, whose inversion is `b` itself.  So the
seam is a letter beside its own inverse, which is what cyclic reduction
forbids.

No parity split and no indexing: the argument never looks past the two end
letters, and it is uniform in the length, the length-one word `[x]` included
(there `b` is both the first letter and the last, and the seam condition reads
`x ≠ invLetter x`). -/
theorem invRev_ne_self_of_isCyclicallyReduced {r : List (α × Bool)}
    (hcyc : FreeGroup.IsCyclicallyReduced r) (hne : r ≠ []) :
    FreeGroup.invRev r ≠ r := by
  intro hcon
  obtain ⟨b, hb⟩ : ∃ b, r.head? = some b := by
    cases r with
    | nil => exact absurd rfl hne
    | cons x xs => exact ⟨x, rfl⟩
  have hlast : r.getLast? = some (invLetter b) := by
    have h := getLast?_invRev r
    rw [hcon, hb] at h
    simpa using h
  exact (isReduced_step_iff.mp (hcyc.2 (invLetter b) hlast b hb))
    (invLetter_invLetter b).symm

/-- **A family with a nonempty relator has two distinct symmetrized relators.**

The nondegeneracy side condition, discharged: take the relator and its formal
inverse, both in the symmetrization by `invRev_mem_symmetrization`, distinct by
`invRev_ne_self_of_isCyclicallyReduced`.

`GreendlingerDehn.ne_nil_of_metricSmallCancellation` takes this as a hypothesis
rather than proving it, so every consumer of that lemma can now discharge it the
same way; here it is what removes the last non-residual hypothesis from the
gate. -/
theorem exists_two_distinct_symmetrization {R : Set (List (α × Bool))}
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hex : ∃ r ∈ R, r ≠ []) :
    ∃ s₁ ∈ symmetrization R, ∃ s₂ ∈ symmetrization R, s₁ ≠ s₂ := by
  obtain ⟨r, hr, hrne⟩ := hex
  have hrmem : r ∈ symmetrization R := subset_symmetrization R hr
  exact ⟨FreeGroup.invRev r, invRev_mem_symmetrization hrmem, r, hrmem,
    invRev_ne_self_of_isCyclicallyReduced (hcyc r hr) hrne⟩

/-! ## 2.  The arithmetic, `λ`-parameterized

These are the twins of `GreendlingerMaxConjugator`'s inequalities.  Each of them
is a pure rational inequality with the lengths abstracted, so the arithmetic can
be read on its own, exactly as `TorsionDescent.residual_empty_of_lam_le_eighth`
is read on its own at the other end of the lane.
-/

/-- **A budget becomes the sharp bound.**  Whatever a rotation of length `T`
loses, if the total loss is under `3λ·T` then what stands is over `(1 − 3λ)·T`,
which is the arc the sharp conclusion asks for.  Every producer below routes
through this. -/
theorem survivor_gt_sharp {lam T loss : ℚ} (h : loss < 3 * lam * T) :
    (1 - 3 * lam) * T < T - loss := by linarith

/-- **One piece and nothing else.**  A single loss under `λ·T` is a fortiori
under `3λ·T`: the piece bound forces `λ·T > 0`, so the two remaining thirds of
the budget are free.  This is the free case of the descent, where the whole
rotation stands and only the offset is spent. -/
theorem one_piece_budget {lam x T : ℚ} (hx0 : 0 ≤ x) (hx : x < lam * T) :
    x < 3 * lam * T := by linarith

/-- **Two pieces leave the sharp arc, with room.**  The `λ`-twin of
`keeps_of_two_pieces`, which says that two sixths leave two thirds.  Here two
losses each under `λ·T` come to under `2λ·T`, a whole `λ·T` inside the budget
`3λ·T` --- so the maximiser's configuration, where both losses are pieces
outright, is not the one that pins the constant. -/
theorem two_pieces_budget {lam x y T : ℚ} (hx0 : 0 ≤ x)
    (hx : x < lam * T) (hy : y < lam * T) : x + y < 3 * lam * T := by linarith

/-- **Three pieces are exactly the budget.**  The `λ`-twin of
`keeps_of_three_pieces`, which says that three sixths are a half only in the
limit the strict bound never reaches.  Here three losses each under `λ·T` come
to under `3λ·T` and no positivity hypothesis is needed: the inequality is
strict on the nose.

This is the configuration that fixes the coefficient `1 − 3λ`. -/
theorem three_pieces_budget {lam x₁ x₂ y T : ℚ}
    (h1 : x₁ < lam * T) (h2 : x₂ < lam * T) (hy : y < lam * T) :
    x₁ + x₂ + y < 3 * lam * T := by linarith

/-- **The three-piece budget is tight**, so `1 − 3λ` is not a rounding of
something better.  With the piece bounds relaxed from `<` to `≤` the three
losses reach `3λ·T` exactly and the conclusion fails.  Machine-checked, in the
same spirit as `TorsionDescent.half_form_residual_satisfiable`: the constant
cannot be improved by rearranging the hypotheses, only by changing them. -/
theorem three_pieces_budget_is_tight {lam T : ℚ} :
    ¬ ∀ x₁ x₂ y : ℚ, x₁ ≤ lam * T → x₂ ≤ lam * T → y ≤ lam * T →
      x₁ + x₂ + y < 3 * lam * T := by
  intro h
  have hcon := h (lam * T) (lam * T) (lam * T) le_rfl le_rfl le_rfl
  linarith

/-- **A hug and a piece do not cover a rotation**, at a general constant.  The
`λ`-twin of `no_overrun_of_hug_and_piece`.  A hug is at most half, a piece is
under `λ·T ≤ T/6`, and a half and a sixth leave a third standing --- so the
`λ ≤ 1/6` band is what this inequality spends, and it is the only place below
where the band is spent for a reason other than comparing `1 − 3λ` with `1/2`. -/
theorem no_overrun_of_hug_and_piece_sharp {lam h p T : ℚ} (hlam : lam ≤ 1 / 6)
    (hT : 0 < T) (hhug : 2 * h ≤ T) (hpiece : p < lam * T)
    (hcover : T ≤ h + p) : False := by
  have h6 : lam * T ≤ 1 / 6 * T := mul_le_mul_of_nonneg_right hlam hT.le
  linarith

/-- **A block overruns at most one factor**, at a general constant.  The
`λ`-twin of `not_second_overrun`.  To pass the factor it landed in, the block
must eat everything that factor has left: `(1 − λ)·T < p + L`, with `p` the
piece it eats and `L` the loss that factor took at its own far junction.  But
`L = hug + pc` with `2·hug + pc ≤ T` and `pc < λ·T` bounds `L` by
`(T + λ·T)/2`, and adding `p < λ·T` keeps `p + L` under `T/2 + 3λ·T/2`.  The two
are contradictory as soon as `λ < 1/5`, so the `1/6` band clears it with room
--- the `ℕ` reading of the same fact is a sixth and seven twelfths against five
sixths. -/
theorem not_second_overrun_sharp {lam p L hug pc T : ℚ} (hlam : lam ≤ 1 / 6)
    (hT : 0 < T) (hpass : (1 - lam) * T < p + L) (hp : p < lam * T)
    (hL : L = hug + pc) (hmeet : 2 * hug + pc ≤ T) (hpc : pc < lam * T) :
    False := by
  have h6 : lam * T ≤ 1 / 6 * T := mul_le_mul_of_nonneg_right hlam hT.le
  have h5 : 5 / 6 * T ≤ (1 - lam) * T :=
    mul_le_mul_of_nonneg_right (by linarith) hT.le
  linarith

/-- **Calibration against the torsion residual.**  The configuration of
`TorsionDescent.half_form_residual_satisfiable` is a relator of length `25` with
an arc of `13`, and `TorsionDescent.half_form_witness_dies_at_eighth` records
that it is the sharp conjunct which fails there.  What the twins above deliver
at `λ = 1/8` on that relator is an arc past `18.75`, because two pieces cost at
most `25/8` each --- comfortably past the `15.625` the residual branch needs and
far past the `13` the half form offers.

So the conjunct that the half form cannot supply is exactly the one recovered
here, on the very configuration that exhibits the gap. -/
theorem two_pieces_beat_the_half_form_witness :
    ((1 : ℚ) - 3 * (1 / 8)) * 25 < 25 - (25 / 8 + 25 / 8) ∧
      ¬ ((1 : ℚ) - 3 * (1 / 8)) * 25 < 13 := by
  norm_num

/-! ## 3.  The located conclusion, at the sharp constant -/

/-- **The Greendlinger conclusion, located, at the sharp constant.**  The
`λ`-twin of `GreendlingerAt`: the word splits as `A ++ u ++ C` with `A` at least
`n` letters long and `u` more than `(1 − 3λ)` of a symmetrized relator.

Position is what the descent inherits and the bound is what the torsion descent
spends, and the two are independent: §4 separates them so that the moves which
only shift position are proved once. -/
def GreendlingerAtSharp (R : Set (List (α × Bool))) (lam : ℚ) (n : ℕ)
    (w : List (α × Bool)) : Prop :=
  ∃ A u C : List (α × Bool), w = A ++ u ++ C ∧ n ≤ A.length ∧
    ∃ s ∈ symmetrization R, u <+: s ∧
      (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ)

/-- Forgetting where the subword is gives back the sharp gate's own
conclusion, in the shape `GreendlingerConclusionSharp` quantifies. -/
theorem greendlingerSharp_of_greendlingerAtSharp {R : Set (List (α × Bool))}
    {lam : ℚ} {n : ℕ} {w : List (α × Bool)}
    (h : GreendlingerAtSharp R lam n w) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
  obtain ⟨A, u, C, hw, -, s, hs, hpre, hlt⟩ := h
  refine ⟨s, hs, u, ⟨A, C, ?_⟩, hpre, hlt⟩
  rw [hw]

/-- A subword located past `n` is located past anything shorter. -/
theorem GreendlingerAtSharp.mono {R : Set (List (α × Bool))} {lam : ℚ}
    {m n : ℕ} {w : List (α × Bool)} (h : GreendlingerAtSharp R lam n w)
    (hmn : m ≤ n) : GreendlingerAtSharp R lam m w := by
  obtain ⟨A, u, C, hw, hlen, hs⟩ := h
  exact ⟨A, u, C, hw, le_trans hmn hlen, hs⟩

/-- **The sharp located form implies the half located form**, for any constant
at most `1/6`.  The located analogue of
`TorsionDescent.greendlingerConclusion_of_sharp`, and the reason the sharp layer
supersedes rather than duplicates the half layer: a proof of
`CascadeLandingSharp` discharges `CascadeLanding`'s consumers too. -/
theorem greendlingerAt_of_greendlingerAtSharp {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 6) {n : ℕ} {w : List (α × Bool)}
    (h : GreendlingerAtSharp R lam n w) : GreendlingerAt R n w := by
  obtain ⟨A, u, C, hw, hlen, s, hs, hpre, hlt⟩ := h
  refine ⟨A, u, C, hw, hlen, s, hs, hpre, ?_⟩
  have hs0 : (0 : ℚ) ≤ (s.length : ℚ) := Nat.cast_nonneg _
  have hhalf : (1 : ℚ) / 2 * (s.length : ℚ) ≤ (1 - 3 * lam) * (s.length : ℚ) :=
    mul_le_mul_of_nonneg_right (by linarith) hs0
  have hq : (s.length : ℚ) < 2 * (u.length : ℚ) := by linarith
  exact_mod_cast hq

/-! ## 4.  The structural layer, with the bound abstracted

Transport and inheritance never read the arc bound.  Stated at the level of the
decomposition alone they are proved once and serve both forms; stating them
twice, once per bound, would be the duplication this file exists to avoid.
-/

/-- **A subword, located.**  The decomposition half of `GreendlingerAt` and of
`GreendlingerAtSharp`, with the relator and the bound removed: `u` sits in `w`
beginning no earlier than position `n`.

This is what the cascade moves actually manipulate. -/
def LocatedSplit (n : ℕ) (w u : List (α × Bool)) : Prop :=
  ∃ A C : List (α × Bool), w = A ++ u ++ C ∧ n ≤ A.length

/-- A subword located past `n` is located past anything shorter. -/
theorem LocatedSplit.mono {m n : ℕ} {w u : List (α × Bool)}
    (h : LocatedSplit n w u) (hmn : m ≤ n) : LocatedSplit m w u := by
  obtain ⟨A, C, hw, hlen⟩ := h
  exact ⟨A, C, hw, le_trans hmn hlen⟩

/-- The sharp located form is a `LocatedSplit` carrying a bound. -/
theorem GreendlingerAtSharp.locatedSplit {R : Set (List (α × Bool))} {lam : ℚ}
    {n : ℕ} {w : List (α × Bool)} (h : GreendlingerAtSharp R lam n w) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      LocatedSplit n w u ∧ u <+: s ∧
        (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
  obtain ⟨A, u, C, hw, hlen, s, hs, hpre, hlt⟩ := h
  exact ⟨s, hs, u, ⟨A, C, hw, hlen⟩, hpre, hlt⟩

/-- ... and conversely. -/
theorem greendlingerAtSharp_of_locatedSplit {R : Set (List (α × Bool))}
    {lam : ℚ} {n : ℕ} {w u s : List (α × Bool)} (hs : s ∈ symmetrization R)
    (hsplit : LocatedSplit n w u) (hpre : u <+: s)
    (hlt : (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ)) :
    GreendlingerAtSharp R lam n w := by
  obtain ⟨A, C, hw, hlen⟩ := hsplit
  exact ⟨A, u, C, hw, hlen, s, hs, hpre, hlt⟩

/-- The half located form is the same `LocatedSplit` carrying the other bound.
Recorded so that the claim "the structural layer is shared" is checkable: both
forms factor through `LocatedSplit` in both directions, so a structural move
proved for `LocatedSplit` is a move for either. -/
theorem GreendlingerAt.locatedSplit {R : Set (List (α × Bool))} {n : ℕ}
    {w : List (α × Bool)} (h : GreendlingerAt R n w) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      LocatedSplit n w u ∧ u <+: s ∧ s.length < 2 * u.length := by
  obtain ⟨A, u, C, hw, hlen, s, hs, hpre, hlt⟩ := h
  exact ⟨s, hs, u, ⟨A, C, hw, hlen⟩, hpre, hlt⟩

/-- ... and conversely. -/
theorem greendlingerAt_of_locatedSplit {R : Set (List (α × Bool))} {n : ℕ}
    {w u s : List (α × Bool)} (hs : s ∈ symmetrization R)
    (hsplit : LocatedSplit n w u) (hpre : u <+: s)
    (hlt : s.length < 2 * u.length) : GreendlingerAt R n w := by
  obtain ⟨A, C, hw, hlen⟩ := hsplit
  exact ⟨A, u, C, hw, hlen, s, hs, hpre, hlt⟩

/-- **Transport, with the bound abstracted.**  A subword located at or after the
drop survives the drop and lands `N` letters earlier inside whatever precedes
it.  This is `GreendlingerCascade.GreendlingerAt.transport` with the relator and
the bound removed --- the move itself touches neither. -/
theorem LocatedSplit.transport {V u : List (α × Bool)} {n N : ℕ}
    (h : LocatedSplit n V u) (A : List (α × Bool)) (hN : N ≤ n) :
    LocatedSplit (A.length + (n - N)) (A ++ V.drop N) u := by
  obtain ⟨X, C, hV, hXlen⟩ := h
  refine ⟨A ++ X.drop N, C, ?_, ?_⟩
  · rw [hV, List.append_assoc, drop_append_of_le N X (u ++ C) (by omega)]
    simp only [List.append_assoc]
  · rw [List.length_append, List.length_drop]
    omega

/-- **Inheritance, with the bound abstracted.**  A subword of what the rest of
the product spells, beginning at or after the block `M` the leading factor
destroys, survives that factor and lands at position `|c| + j`.  This is
`GreendlingerThreeFactor.greendlingerAt_inherit` with the relator and the bound
removed. -/
theorem LocatedSplit.inherit {c t P' M B' W u : List (α × Bool)} {n j : ℕ}
    (heq : palindrome c t = P' ++ M)
    (hW : W = FreeGroup.invRev M ++ B')
    (hhigh : M.length + j ≤ c.length + t.length)
    (hn : M.length ≤ n) (h : LocatedSplit n W u) :
    LocatedSplit (c.length + j) (P' ++ B') u := by
  obtain ⟨A, C, hWeq, hAlen⟩ := h
  have hMl : (FreeGroup.invRev M).length = M.length := FreeGroup.invRev_length
  have hMpre : FreeGroup.invRev M <+: W := ⟨B', hW.symm⟩
  have hApre : A <+: W := ⟨u ++ C, by rw [hWeq, List.append_assoc]⟩
  obtain ⟨D, hD⟩ := List.prefix_of_prefix_length_le hMpre hApre (by omega)
  have hlenA : (FreeGroup.invRev M).length + D.length = A.length := by
    have hb := congrArg List.length hD
    rw [List.length_append] at hb
    exact hb
  have hsplit : FreeGroup.invRev M ++ B'
      = FreeGroup.invRev M ++ (D ++ (u ++ C)) := by
    rw [← hW, hWeq, ← hD]
    simp only [List.append_assoc]
  have hB' : B' = D ++ (u ++ C) := List.append_cancel_left hsplit
  have hpal : (palindrome c t).length = c.length + t.length + c.length := by
    simp [palindrome, FreeGroup.invRev_length, Nat.add_assoc]
  have hlenP : P'.length + M.length = c.length + t.length + c.length := by
    have hb := congrArg List.length heq
    rw [List.length_append, hpal] at hb
    omega
  refine ⟨P' ++ D, C, ?_, ?_⟩
  · rw [hB']
    simp only [List.append_assoc]
  · rw [List.length_append]
    omega

/-- **Transport at the sharp constant**, read off the shared structural move. -/
theorem GreendlingerAtSharp.transport {R : Set (List (α × Bool))} {lam : ℚ}
    {V : List (α × Bool)} {n N : ℕ} (h : GreendlingerAtSharp R lam n V)
    (A : List (α × Bool)) (hN : N ≤ n) :
    GreendlingerAtSharp R lam (A.length + (n - N)) (A ++ V.drop N) := by
  obtain ⟨s, hs, u, hsplit, hpre, hlt⟩ := h.locatedSplit
  exact greendlingerAtSharp_of_locatedSplit hs (hsplit.transport A hN) hpre hlt

/-- **Inheritance at the sharp constant**, read off the shared structural
move. -/
theorem greendlingerAtSharp_inherit {R : Set (List (α × Bool))} {lam : ℚ}
    {c t P' M B' W : List (α × Bool)} {n j : ℕ}
    (heq : palindrome c t = P' ++ M)
    (hW : W = FreeGroup.invRev M ++ B')
    (hhigh : M.length + j ≤ c.length + t.length)
    (hn : M.length ≤ n) (h : GreendlingerAtSharp R lam n W) :
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') := by
  obtain ⟨s, hs, u, hsplit, hpre, hlt⟩ := h.locatedSplit
  exact greendlingerAtSharp_of_locatedSplit hs
    (hsplit.inherit heq hW hhigh hn) hpre hlt

/-! ## 5.  The producers, at the sharp constant -/

/-- **The quantitative case, located, with slack, at the sharp constant.**  The
`λ`-twin of `greendlingerAt_of_bounded_cancellation`.  A cancellation reaching
`k` letters past the trailing conjugator leaves `t.take (|t| − k)` standing, and
the subword may be started `j` letters later still, provided the two together
stay inside the budget `3λ·|t|`.

The half form's hypothesis is `2(k + j) < |t|`; this is that inequality with the
budget written in the constant the conclusion is stated at.  The band
`λ ≤ 1/6` is used only to know `3λ·|t| ≤ |t|/2`, so that `k + j` does not
overrun the rotation it is measured against. -/
theorem greendlingerAtSharp_of_bounded_cancellation {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 6)
    {c t P' M B' : List (α × Bool)} {k j : ℕ}
    (ht : t ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hlen : M.length ≤ (FreeGroup.invRev c).length + k)
    (hk : (k : ℚ) + (j : ℚ) < 3 * lam * (t.length : ℚ)) :
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') := by
  have hT0 : (0 : ℚ) ≤ (t.length : ℚ) := Nat.cast_nonneg _
  have h3 : 3 * lam * (t.length : ℚ) ≤ 1 / 2 * (t.length : ℚ) :=
    mul_le_mul_of_nonneg_right (by linarith) hT0
  have hkjq : ((k + j : ℕ) : ℚ) < (t.length : ℚ) := by
    push_cast
    linarith
  have hkj : k + j < t.length := by exact_mod_cast hkjq
  have hkle : k ≤ t.length := by omega
  have hjle : j ≤ t.length := by omega
  obtain ⟨d, hP'⟩ := exists_split_take_of_bounded_cancellation heq hkle hlen
  have hsplit : t.take (t.length - k)
      = t.take j ++ (t.drop j).take (t.length - k - j) := by
    have hb := take_add_split j t (t.length - k - j)
    rw [show j + (t.length - k - j) = t.length - k from by omega] at hb
    exact hb
  have hlenu : ((t.drop j).take (t.length - k - j)).length = t.length - k - j := by
    rw [List.length_take, List.length_drop]
    omega
  refine ⟨c ++ t.take j, (t.drop j).take (t.length - k - j), d ++ B', ?_, ?_,
    t.rotate j, rotate_mem_symmetrization ht j, ?_, ?_⟩
  · rw [hP', hsplit]
    simp only [List.append_assoc]
  · rw [List.length_append, List.length_take]
    omega
  · rw [List.rotate_eq_drop_append_take hjle]
    exact (List.take_prefix _ _).trans ⟨t.take j, rfl⟩
  · rw [List.length_rotate, hlenu,
      Nat.cast_sub (show j ≤ t.length - k from by omega), Nat.cast_sub hkle]
    linarith

/-- **The free case, located, with slack, at the sharp constant.**  The `λ`-twin
of `greendlingerAt_of_short_cancellation`: a cancellation confined to the
trailing conjugator leaves the whole rotation standing, so any offset under
`λ·|t|` is available --- `one_piece_budget` says a single `λ` is inside the
budget `3λ`. -/
theorem greendlingerAtSharp_of_short_cancellation {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 6)
    {c t P' M B' : List (α × Bool)} {j : ℕ}
    (ht : t ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hlen : M.length ≤ (FreeGroup.invRev c).length)
    (hj : (j : ℚ) < lam * (t.length : ℚ)) :
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') := by
  refine greendlingerAtSharp_of_bounded_cancellation (k := 0) hlam ht heq
    (by omega) ?_
  have hb := one_piece_budget (Nat.cast_nonneg _) hj
  push_cast
  linarith

/-- **Two pieces, located, at the sharp constant.**  The maximiser's
configuration: a loss that is a piece at each side of the offset.  This is the
sharp reading of `keeps_of_two_pieces`, and it clears the budget with `λ·|t|` to
spare. -/
theorem greendlingerAtSharp_of_two_pieces {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 6)
    {c t P' M B' : List (α × Bool)} {x j : ℕ}
    (ht : t ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hM : M.length ≤ (FreeGroup.invRev c).length + x)
    (hx : (x : ℚ) < lam * (t.length : ℚ))
    (hj : (j : ℚ) < lam * (t.length : ℚ)) :
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') :=
  greendlingerAtSharp_of_bounded_cancellation hlam ht heq hM
    (two_pieces_budget (Nat.cast_nonneg _) hx hj)

/-- **Three pieces, located, at the sharp constant.**  The overrun
configuration, where the loss on one side is two pieces rather than one.  This
is the sharp reading of `keeps_of_three_pieces`, and it is the case that pins
the coefficient: the budget is met exactly, with nothing to spare. -/
theorem greendlingerAtSharp_of_three_pieces {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 6)
    {c t P' M B' : List (α × Bool)} {x₁ x₂ j : ℕ}
    (ht : t ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hM : M.length ≤ (FreeGroup.invRev c).length + (x₁ + x₂))
    (h1 : (x₁ : ℚ) < lam * (t.length : ℚ))
    (h2 : (x₂ : ℚ) < lam * (t.length : ℚ))
    (hj : (j : ℚ) < lam * (t.length : ℚ)) :
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') := by
  refine greendlingerAtSharp_of_bounded_cancellation hlam ht heq hM ?_
  have hb := three_pieces_budget h1 h2 hj
  push_cast
  linarith

/-! ## 6.  The junction fact, at the sharp constant -/

/-- **What a block is matched against at a maximal junction**, at a general
constant.  The `λ`-twin of `MaximalJunction`: at a factor whose conjugator is at
least as long as the neighbouring one, the part of its rotation the junction
destroys is matched letter for letter against the neighbour's rotation, hence is
a piece, hence under `λ` of it.

The statement is one-sided; the argument applies it twice, once at each side of
the maximising factor. -/
def MaximalJunctionSharp (R : Set (List (α × Bool))) (lam : ℚ) : Prop :=
  ∀ (c t c' t' : List (α × Bool)) (x : ℕ),
    t ∈ symmetrization R → t' ∈ symmetrization R →
    c'.length ≤ c.length →
    IsPiece (symmetrization R) (t.take x) ∨ x = 0 →
    (x : ℚ) < lam * (t.length : ℚ)

/-- **The located conclusion at the maximising factor, at the sharp constant.**
The `λ`-twin of `greendlingerAt_of_maximalJunction`.  Given the junction fact on
both sides, the factor with the longest conjugator keeps more than `(1 − 3λ)` of
its rotation, which is more than the sharp gate asks for.

Nothing else is needed once both losses are pieces: the proof is
`two_pieces_budget`, exactly as the half form's is `keeps_of_two_pieces`. -/
theorem greendlingerAtSharp_of_maximalJunctionSharp {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 6)
    {c t P' M B' : List (α × Bool)} {x j : ℕ}
    (ht : t ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hM : M.length ≤ (FreeGroup.invRev c).length + x)
    (hx : (x : ℚ) < lam * (t.length : ℚ))
    (hj : (j : ℚ) < lam * (t.length : ℚ)) :
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') :=
  greendlingerAtSharp_of_two_pieces hlam ht heq hM hx hj

/-! ## 7.  The landing site and the cascade, at the sharp constant -/

/-- **The block lands in a later factor's conjugator**, at a general constant.
The `λ`-twin of `LandsIn`: the only `1/6` in that definition is the bound on how
far into the landing factor's rotation the block may stop, and that bound is a
piece bound, so it moves with the constant.

Everything else --- the cascade decomposition, minimality of the landing
expression, the length that makes the descent terminate --- is `λ`-free and
copied unchanged. -/
def LandsInSharp [DecidableEq α] (R : Set (List (α × Bool))) (lam : ℚ)
    (b : ℕ) (V : List (α × Bool)) (m : ℕ) : Prop :=
  ∃ (c' t' : List (α × Bool)) (f : List (FreeGroup α × List (α × Bool)))
    (A : List (α × Bool)) (N i : ℕ),
    f.length < m ∧
    V = A ++ (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop N ∧
    t' ∈ symmetrization R ∧
    FreeGroup.IsReduced (palindrome c' t') ∧
    IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f)
      (conjEval ((FreeGroup.mk c', t') :: f)) ∧
    (i : ℚ) < lam * (t'.length : ℚ) ∧ N ≤ c'.length + i ∧
    b + N ≤ A.length + c'.length + i

/-- A landing site for a block serves for any shorter block. -/
theorem LandsInSharp.of_le [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} {b b' : ℕ} {V : List (α × Bool)} {m : ℕ}
    (h : LandsInSharp R lam b V m) (hle : b' ≤ b) : LandsInSharp R lam b' V m := by
  obtain ⟨c', t', f, A, N, i, hf, hV, ht', hredp', hmin, hi, hN, hM⟩ := h
  exact ⟨c', t', f, A, N, i, hf, hV, ht', hredp', hmin, hi, hN, by omega⟩

/-- A landing site found among fewer factors serves among more. -/
theorem LandsInSharp.mono [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} {b : ℕ} {V : List (α × Bool)} {m m' : ℕ}
    (h : LandsInSharp R lam b V m) (hm : m ≤ m') : LandsInSharp R lam b V m' := by
  obtain ⟨c', t', f, A, N, i, hf, hV, ht', hredp', hmin, hi, hN, hM⟩ := h
  exact ⟨c', t', f, A, N, i, by omega, hV, ht', hredp', hmin, hi, hN, hM⟩

/-- **The case that needs no jump**, at the sharp constant.  When the block stops
inside the next factor's own conjugator --- or at most `λ` of a rotation past it
--- the tail itself is the landing site.  The `λ`-twin of
`landsIn_of_confined`. -/
theorem landsInSharp_of_confined [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} {c' t' : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {b i m : ℕ}
    (ht' : t' ∈ symmetrization R)
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f)
      (conjEval ((FreeGroup.mk c', t') :: f)))
    (hi : (i : ℚ) < lam * (t'.length : ℚ)) (hfit : b ≤ c'.length + i)
    (hm : f.length < m) :
    LandsInSharp R lam b (conjEval ((FreeGroup.mk c', t') :: f)).toWord m := by
  refine ⟨c', t', f, [], 0, i, hm, ?_, ht', hredp', hmin, hi, by omega, ?_⟩
  · rw [List.drop_zero, List.nil_append]
  · rw [List.length_nil]
    omega

/-- **Where the leading block stops**, at a general constant.  The `λ`-twin of
`CascadeLanding`, and the one hypothesis the sharp descent takes: either the
block leaves enough of the leading rotation standing for the located conclusion
at the sharp bound to come from the leading factor itself, or it stops in a
later factor within `λ` of that factor's rotation past its conjugator.

Word for word `CascadeLanding` with `GreendlingerAt` replaced by
`GreendlingerAtSharp`, `LandsIn` by `LandsInSharp`, and the two offset bounds
`6·j < |t|` read at the family's own constant.  At `λ = 1/6` the two agree. -/
def CascadeLandingSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (j : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (j : ℚ) < lam * (t.length : ℚ) →
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') ∨
      (M.length + j ≤ c.length + t.length ∧
        LandsInSharp R lam M.length (conjEval e).toWord e.length)

/-- **The descent, at the sharp constant.**  The `λ`-twin of
`greendlingerAt_of_cascadeLanding`: for a minimal expression of any length whose
leading factor is in palindromic normal form, the reduced word contains more
than `(1 − 3λ)` of a symmetrized relator, beginning at or after position
`|c| + j` for every offset `j` under `λ` of the leading rotation.

The induction is the same one, factor by factor along the cascade; only the
three producers and the two structural moves it calls have moved to the sharp
form. -/
theorem greendlingerAtSharp_of_cascadeLandingSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hland : CascadeLandingSharp R lam) :
    ∀ (n : ℕ) (e : List (FreeGroup α × List (α × Bool)))
      (c t w : List (α × Bool)) (j : ℕ),
      e.length ≤ n →
      FreeGroup.IsReduced w → t ∈ symmetrization R →
      FreeGroup.IsReduced (palindrome c t) →
      IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) (FreeGroup.mk w) →
      (j : ℚ) < lam * (t.length : ℚ) →
      GreendlingerAtSharp R lam (c.length + j) w := by
  intro n
  induction n with
  | zero =>
      intro e c t w j hlen hw ht hredp hmin hj
      cases e with
      | cons x e' =>
          simp only [List.length_cons] at hlen
          exact absurd hlen (by omega)
      | nil =>
          obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
            exists_leading_cancellation hw hredp hmin.2.1
          have hnil : FreeGroup.invRev M ++ B' = [] := by
            rw [← hgw, conjEval_nil]
            exact FreeGroup.toWord_eq_nil_iff.mpr rfl
          have hz := congrArg List.length hnil
          rw [List.length_append, FreeGroup.invRev_length,
            List.length_nil] at hz
          rw [hwe]
          exact greendlingerAtSharp_of_short_cancellation hlam ht heq (by omega) hj
  | succ n ih =>
      intro e c t w j hlen hw ht hredp hmin hj
      obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
        exists_leading_cancellation hw hredp hmin.2.1
      have hcl : (FreeGroup.invRev c).length = c.length := FreeGroup.invRev_length
      rw [hwe]
      rcases le_or_gt M.length (FreeGroup.invRev c).length with hshort | hlong
      · exact greendlingerAtSharp_of_short_cancellation hlam ht heq hshort hj
      · rcases hland c t e (FreeGroup.mk w) P' M B' j hmin ht hredp heq hgw
            (by omega) hj with hdone | ⟨hhigh, hlands⟩
        · exact hdone
        · obtain ⟨c', t', f, A, N, i, hf, hV, ht', hredp', hminf, hi, hN, hMb⟩ :=
            hlands
          have hIH := ih f c' t'
            (conjEval ((FreeGroup.mk c', t') :: f)).toWord i
            (by omega) FreeGroup.isReduced_toWord ht' hredp'
            (by rw [FreeGroup.mk_toWord]; exact hminf) hi
          have htrans := hIH.transport A hN
          rw [← hV] at htrans
          exact greendlingerAtSharp_inherit heq hgw hhigh (by omega) htrans

/-- **The sharp conclusion from a minimal expression of any length.**  The
`λ`-twin of `greendlinger_of_cascadeLanding`.

`0 < lam` is what the offset `j = 0` costs: the free case leaves the whole
rotation standing, and the sharp bound then asks `(1 − 3λ)·|t| < |t|`, which is
`0 < 3λ·|t|`.  `lam_pos_of_metric` supplies it from the metric condition on any
family with anything to prove. -/
theorem greendlingerSharp_of_cascadeLandingSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hland : CascadeLandingSharp R lam)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {e : List (FreeGroup α × List (α × Bool))}
    (hmin : IsMinimalConjExpr R e (FreeGroup.mk w)) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
  cases e with
  | nil =>
      exfalso
      have hb := hmin.2.1
      rw [conjEval_nil] at hb
      have h1 : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
        rw [← FreeGroup.one_eq_mk]
        exact hb.symm
      have h2 := FreeGroup.reduce.sound h1
      rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
      exact hwne h2
  | cons x e'' =>
      obtain ⟨x₁, s₁⟩ := x
      obtain ⟨c, t, ht, hredp, hmin'⟩ := exists_palindromic_head hR hRne hmin
      have htpos : 0 < t.length :=
        List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
      have hjq : ((0 : ℕ) : ℚ) < lam * (t.length : ℚ) := by
        have htq : (0 : ℚ) < (t.length : ℚ) := by exact_mod_cast htpos
        simpa using mul_pos hlam0 htq
      exact greendlingerSharp_of_greendlingerAtSharp
        (greendlingerAtSharp_of_cascadeLandingSharp hlam hland e''.length e'' c t
          w 0 le_rfl hw ht hredp hmin' hjq)

/-- **The sharp gate, for a `C'(λ)` family whose leading blocks land.**  The
`λ`-twin of `greendlingerConclusion_of_cascadeLanding`, and the statement
`GreendlingerFreeGate.SharpGreendlingerGate` is the universal closure of. -/
theorem greendlingerConclusionSharp_of_cascadeLandingSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hland : CascadeLandingSharp R lam) :
    GreendlingerConclusionSharp R lam := by
  intro w hw hwne hmem
  obtain ⟨n, hcount⟩ := (mem_normalClosure_iff R (FreeGroup.mk w)).mp hmem
  obtain ⟨e₀, hv₀, -, he₀⟩ :=
    (isConjProduct_iff_exists_conjExpr n (FreeGroup.mk w)).mp hcount
  obtain ⟨e, hmin⟩ := exists_isMinimalConjExpr ⟨e₀, hv₀, he₀⟩
  exact greendlingerSharp_of_cascadeLandingSharp hR hRne hlam0 hlam hland hw hwne
    hmin

/-! ## 8.  The end state: the sharp gate, and its two consumers -/

/-- **The sharp gate, from the `λ`-form residual.**  One named hypothesis and
nothing else: `hland`, the real residual `CascadeLandingSharp`, the `λ`-twin of
`CascadeLanding`.

Two things a gate could have been asked for are proved instead of assumed.

* **Nondegeneracy.**  `exists_two_distinct_symmetrization` supplies the two
  distinct symmetrized relators that `ne_nil_of_metric_lam` and
  `lam_pos_of_metric` consume, so `∀ r ∈ R, r ≠ []` and `0 < lam` are both
  derived from the metric condition rather than named.  Both are then *handed
  to* `hland`, which is why the residual family may assume them: the deep-side
  reduction needs `∀ r ∈ R, r ≠ []` (through `swallow_bound_of_minimal` and
  `not_absorb_of_minimal`), and the assembly has already paid for it.
* **The degenerate branch**, where every relator is empty: the normal closure is
  then trivial and no nonempty reduced word lies in it, so the conclusion holds
  with nothing to produce.  Naming that branch as a hypothesis would have made
  the bundle unsatisfiable, which is the one shape a gate must not have. -/
theorem sharpGreendlingerGate_of_cascadeLandingSharp [DecidableEq α]
    (hland : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → CascadeLandingSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate α := by
  intro R lam hcyc hlam hmetric
  by_cases hex : ∃ r ∈ R, r ≠ []
  · obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := exists_two_distinct_symmetrization hcyc hex
    obtain ⟨r, hr, hrne⟩ := hex
    have hlam0 : 0 < lam :=
      lam_pos_of_metric hmetric hs₁ hs₂ hne (subset_symmetrization R hr) hrne
    have hRne : ∀ q ∈ R, q ≠ [] := fun q hq =>
      ne_nil_of_metric_lam hmetric hs₁ hs₂ hne (subset_symmetrization R hq)
    exact greendlingerConclusionSharp_of_cascadeLandingSharp hcyc hRne hlam0 hlam
      (hland R lam hcyc hRne hlam0 hlam hmetric)
  · intro w hw hwne hmem
    exfalso
    push Not at hex
    have hsub : FreeGroup.mk '' R ⊆
        ((⊥ : Subgroup (FreeGroup α)) : Set (FreeGroup α)) := by
      rintro _ ⟨r, hr, rfl⟩
      have hone : FreeGroup.mk r = (1 : FreeGroup α) := by
        rw [hex r hr, ← FreeGroup.one_eq_mk]
      simp [hone]
    have hb := Subgroup.normalClosure_le_normal hsub hmem
    rw [Subgroup.mem_bot] at hb
    have h1 : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
      rw [hb]
      exact FreeGroup.one_eq_mk
    have h2 := FreeGroup.reduce.sound h1
    rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
    exact hwne h2

/-- The gate on the router's own alphabet, which is the instance every
construction in this repository consumes. -/
theorem sharpGreendlingerGate_fin_two_of_cascadeLandingSharp
    (hland : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → CascadeLandingSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) :=
  sharpGreendlingerGate_of_cascadeLandingSharp hland

/-- **Torsion-freeness, from the `λ`-form residual.**  The composition this file
exists to make possible: the sharp gate feeds
`GreendlingerFreeGate.torsionFree_of_sharpGate`, which is
`TorsionDescent.isPowerTorsionFree_of_sharp` in one line, and the residual case
that the half form leaves open is empty at `λ ≤ 1/8`. -/
theorem torsionFree_of_cascadeLandingSharp [DecidableEq α]
    (hland : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → CascadeLandingSharp R lam)
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hmetric : MetricSmallCancellation R lam)
    (hnpp : GreendlingerFreeGate.NoProperPower R) :
    IsPowerTorsionFree
      (FreeGroup α ⧸ Subgroup.normalClosure (FreeGroup.mk '' R)) :=
  GreendlingerFreeGate.torsionFree_of_sharpGate
    (sharpGreendlingerGate_of_cascadeLandingSharp hland) hlam8 hcyc hmetric
    hnpp

/-- **Both router obligations, from the `λ`-form residual.**  Injectivity on the
protected set and torsion-freeness of the quotient, which are the two
word-combinatorial fields of `RoutingLemmaData`, from the same gate.  When
`CascadeLandingSharp` is proved this loses its hypotheses and no signature
downstream moves. -/
theorem router_conclusions_of_cascadeLandingSharp [DecidableEq α]
    (hland : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → CascadeLandingSharp R lam)
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hmetric : MetricSmallCancellation R lam)
    (hnpp : GreendlingerFreeGate.NoProperPower R)
    (P : Set (FreeGroup α))
    (hshort : ∀ r ∈ symmetrization R, ∀ x ∈ P, ∀ y ∈ P,
      2 * FreeGroup.norm (x / y) ≤ r.length) :
    Set.InjOn
        (QuotientGroup.mk' (Subgroup.normalClosure (FreeGroup.mk '' R))) P ∧
      IsPowerTorsionFree
        (FreeGroup α ⧸ Subgroup.normalClosure (FreeGroup.mk '' R)) :=
  GreendlingerFreeGate.router_conclusions_of_sharpGate
    (sharpGreendlingerGate_of_cascadeLandingSharp hland) hlam8 hcyc hmetric
    hnpp P hshort

/-! ## 9.  Down to the live residuals: the deep arc and the (β) landing

`Sofic.GreendlingerAlphaPlumb` reduces `CascadeLanding` to `DeepArcSource` and
`LandingProductionBeta` by discharging the conjugator-absorbed case against the
descent's own context.  Its plumbing is `λ`-free and is consumed here unchanged:
`ConjugatorAbsorbedSite` is word geometry and names no constant,
`eaten_prefix_orientation` and `invRev_ne_rotate_of_minimal` are word facts, and
`exists_cascade_split` is the cascade decomposition.

The one place the constant enters that route is `six_mul_intrusion_lt`, the
double piece bound on the intrusion, and the three predicates that quote it.
Those are twinned below and nothing else is.
-/

/-- **The double piece bound, at a general constant.**  The `λ`-twin of
`GreendlingerDeepestMatch.six_mul_intrusion_lt`: the deep segment `E` is eaten
off the head rotation and reappears, formally inverted, inside a rotation of the
landing relator, so it is a piece and is bounded against *both* --- the head
rotation and the landing one.

The head half is what places the block inside the head rotation; the landing
half is the offset field of `LandsInSharp`. -/
theorem intrusion_lt_of_metric {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {t t' E : List (α × Bool)} {k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hEt : E <:+ t)
    (hintr : FreeGroup.invRev E <+: t'.rotate k)
    (hne : FreeGroup.invRev t ≠ t'.rotate k) :
    (E.length : ℚ) < lam * (t.length : ℚ) ∧
      (E.length : ℚ) < lam * (t'.length : ℚ) := by
  have hpiece : IsPiece (symmetrization R) (FreeGroup.invRev E) :=
    isPiece_of_overlap ht ht' hEt hintr hne
  have hhead := hmetric (FreeGroup.invRev E) hpiece (FreeGroup.invRev t)
    (invRev_mem_symmetrization ht) (invRev_prefix_of_suffix hEt)
  have hland := hmetric (FreeGroup.invRev E) hpiece (t'.rotate k)
    (rotate_mem_symmetrization ht' k) hintr
  rw [FreeGroup.invRev_length, FreeGroup.invRev_length] at hhead
  rw [FreeGroup.invRev_length, List.length_rotate] at hland
  exact ⟨hhead, hland⟩

/-- **The `i_c = 0` landing, at the sharp constant.**  The `λ`-twin of
`GreendlingerDeepestMatch.landsIn_of_conjugatorAbsorbed`: the same landing data,
with the landing half of the double piece bound serving as the offset field of
`LandsInSharp` instead of the sixth-bound field of `LandsIn`.  Everything else
is cascade bookkeeping and is untouched. -/
theorem landsInSharp_of_conjugatorAbsorbed [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {t t' c' E A M : List (α × Bool)} {k N : ℕ}
    {e f : List (FreeGroup α × List (α × Bool))}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hEt : E <:+ t)
    (hintr : FreeGroup.invRev E <+: t'.rotate k)
    (hne : FreeGroup.invRev t ≠ t'.rotate k)
    (hf : f.length < e.length)
    (hV : (conjEval e).toWord
      = A ++ (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop N)
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (hmin' : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f)
      (conjEval ((FreeGroup.mk c', t') :: f)))
    (hN : N ≤ c'.length + E.length)
    (hfit : M.length + N ≤ A.length + c'.length + E.length) :
    LandsInSharp R lam M.length (conjEval e).toWord e.length :=
  ⟨c', t', f, A, N, E.length, hf, hV, ht', hredp', hmin',
    (intrusion_lt_of_metric hmetric ht ht' hEt hintr hne).2, hN, hfit⟩

/-- **The landing from the site, at the sharp constant.**  The `λ`-twin of
`landsIn_of_conjugatorAbsorbedSite`.  `ConjugatorAbsorbedSite` is `λ`-free and
is consumed, not restated: the four relator-side facts the landing needs still
come out of minimality and the site alone. -/
theorem landsInSharp_of_conjugatorAbsorbedSite [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {c t E M : List (α × Bool)} {e : List (FreeGroup α × List (α × Bool))}
    {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (ht : t ∈ symmetrization R) (hEt : E <:+ t)
    (hsite : ConjugatorAbsorbedSite c E M e) :
    LandsInSharp R lam M.length (conjEval e).toWord e.length := by
  obtain ⟨e₁, f, c', t', d, q, A, N, he, hredp', hd, hcq, hq, hintr, hV, hN,
    hfit⟩ := hsite
  subst he
  have ht' : t' ∈ symmetrization R := hmin.1 (FreeGroup.mk c', t') (by simp)
  have hdrop :
      ((FreeGroup.mk c, t) :: (e₁ ++ ((FreeGroup.mk c', t') :: f))).drop
        (e₁.length + 1) = (FreeGroup.mk c', t') :: f := by
    rw [List.drop_succ_cons, List.drop_left]
  have hmin' := isMinimalConjExpr_drop (e₁.length + 1)
    ((FreeGroup.mk c, t) :: (e₁ ++ ((FreeGroup.mk c', t') :: f))) g hmin
  rw [hdrop] at hmin'
  have hf : f.length < (e₁ ++ ((FreeGroup.mk c', t') :: f)).length := by
    simp only [List.length_append, List.length_cons]
    omega
  exact landsInSharp_of_conjugatorAbsorbed hmetric ht ht' hEt hintr
    (invRev_ne_rotate_of_minimal hmin hd hcq hq) hf hV hredp' hmin' hN hfit

/-- **The (α) disjunct at the sharp constant.**  The `λ`-twin of
`cascadeLanding_of_conjugatorAbsorbedSite`: the landing side of
`CascadeLandingSharp`'s disjunction, for a head whose block fits and whose
landing site is conjugator-absorbed. -/
theorem cascadeLandingSharp_of_conjugatorAbsorbedSite [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {c t E M P' B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {j : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (ht : t ∈ symmetrization R) (hEt : E <:+ t)
    (hle : M.length + j ≤ c.length + t.length)
    (hsite : ConjugatorAbsorbedSite c E M e) :
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') ∨
      (M.length + j ≤ c.length + t.length ∧
        LandsInSharp R lam M.length (conjEval e).toWord e.length) :=
  Or.inr ⟨hle, landsInSharp_of_conjugatorAbsorbedSite hmetric hmin ht hEt hsite⟩

/-- **The deep arc obligation, at a general constant.**  The `λ`-twin of
`GreendlingerBetaBranch.DeepArcSource`: in the regime where the block outruns
the head palindrome, the located conclusion at the sharp bound must come from
somewhere in the tail. -/
def DeepArcSourceSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (j : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (j : ℚ) < lam * (t.length : ℚ) →
    c.length + t.length < M.length + j →
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B')

/-- **The landing obligation, at a general constant.**  The `λ`-twin of
`GreendlingerBetaBranch.LandingProduction`. -/
def LandingProductionSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (j : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (j : ℚ) < lam * (t.length : ℚ) →
    M.length + j ≤ c.length + t.length →
    LandsInSharp R lam M.length (conjEval e).toWord e.length

/-- **The landing obligation, (β) only, at a general constant.**  The `λ`-twin
of `LandingProductionBeta`: the same predicate with the orientation package
supplied and with the conjugator-absorbed regime excluded, so it is asked only
where conjugator letters reach the landing factor's relator letters.

The orientation fields are `λ`-free and are quoted verbatim from the half-form
predicate; only the offset bound and the conclusion move. -/
def LandingProductionBetaSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' E : List (α × Bool)) (j : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (j : ℚ) < lam * (t.length : ℚ) →
    M.length + j ≤ c.length + t.length →
    M = E ++ FreeGroup.invRev c →
    FreeGroup.invRev M = c ++ FreeGroup.invRev E →
    E <:+ t → 0 < E.length →
    ¬ConjugatorAbsorbedSite c E M e →
    LandsInSharp R lam M.length (conjEval e).toWord e.length

/-- **The landing production with case (α) discharged**, at the sharp constant.
The `λ`-twin of `landingProduction_of_beta`: the case split is on the existence
of the site, the positive branch is the `λ`-free plumbing of
`Sofic.GreendlingerAlphaPlumb` read through the sharp landing, and the negative
branch is the residual predicate. -/
theorem landingProductionSharp_of_betaSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    (hbeta : LandingProductionBetaSharp R lam) :
    LandingProductionSharp R lam := by
  intro c t e g P' M B' j hmin ht hredp heq htail hlow hj hle
  obtain ⟨E, hM, hMinv, hEt, -, hEpos⟩ :=
    eaten_prefix_orientation heq hlow (by omega)
  by_cases hsite : ConjugatorAbsorbedSite c E M e
  · exact landsInSharp_of_conjugatorAbsorbedSite hmetric hmin ht hEt hsite
  · exact hbeta c t e g P' M B' E j hmin ht hredp heq htail hlow hj hle hM hMinv
      hEt hEpos hsite

/-- **`CascadeLandingSharp` from the two obligations.**  The `λ`-twin of
`GreendlingerBetaBranch.cascadeLanding_of_deepArc_of_landing`: one inequality
decides which obligation is called, and each is stated over exactly the regime
it owns. -/
theorem cascadeLandingSharp_of_deepArcSharp_of_landingSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hdeep : DeepArcSourceSharp R lam) (hland : LandingProductionSharp R lam) :
    CascadeLandingSharp R lam := by
  intro c t e g P' M B' j hmin ht hredp heq htail hlow hj
  rcases le_or_gt (M.length + j) (c.length + t.length) with hle | hgt
  · exact Or.inr ⟨hle,
      hland c t e g P' M B' j hmin ht hredp heq htail hlow hj hle⟩
  · exact Or.inl (hdeep c t e g P' M B' j hmin ht hredp heq htail hlow hj hgt)

/-- **`CascadeLandingSharp` over (β)-side residuals only.**  The `λ`-twin of
`cascadeLanding_of_deepArc_of_beta`, which is the live assembly entry point:
case (α) contributes nothing to the hypothesis, having been discharged against
the descent's own context. -/
theorem cascadeLandingSharp_of_deepArcSharp_of_betaSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepArcSourceSharp R lam)
    (hbeta : LandingProductionBetaSharp R lam) :
    CascadeLandingSharp R lam :=
  cascadeLandingSharp_of_deepArcSharp_of_landingSharp hdeep
    (landingProductionSharp_of_betaSharp hmetric hbeta)

/-- **The sharp conclusion over (β)-side residuals only.**  The `λ`-twin of
`greendlingerConclusion_of_deepArc_of_beta`, and the statement the gate is the
universal closure of. -/
theorem greendlingerConclusionSharp_of_deepArcSharp_of_betaSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepArcSourceSharp R lam)
    (hbeta : LandingProductionBetaSharp R lam) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_cascadeLandingSharp hR hRne hlam0 hlam
    (cascadeLandingSharp_of_deepArcSharp_of_betaSharp hmetric hdeep hbeta)

/-- **The residual bundle, in the shape the end state consumes.**  Two families
of residuals --- the deep arc and the (β) landing, quantified over every family
the gate is asked about --- become the one `CascadeLandingSharp` family that
`sharpGreendlingerGate_of_cascadeLandingSharp`,
`torsionFree_of_cascadeLandingSharp` and
`router_conclusions_of_cascadeLandingSharp` each take as their `hland`.

So no consumer signature is restated over the (β)-side residuals: this one
theorem is the adapter, and the three end-state theorems above are used as they
stand. -/
theorem cascadeLandingSharp_family_of_deepArcSharp_of_betaSharp [DecidableEq α]
    (hdeep : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepArcSourceSharp R lam)
    (hbeta : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → LandingProductionBetaSharp R lam) :
    ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → CascadeLandingSharp R lam :=
  fun R lam hcyc hRne hlam0 hlam hmetric =>
    cascadeLandingSharp_of_deepArcSharp_of_betaSharp hmetric
      (hdeep R lam hcyc hRne hlam0 hlam hmetric)
      (hbeta R lam hcyc hRne hlam0 hlam hmetric)

/-- **The sharp gate over the live residuals.**  `SharpGreendlingerGate α` from
the deep arc and the (β) landing and nothing else --- these being the `λ`-twins
of exactly the two residuals
`GreendlingerAlphaPlumb.cascadeLanding_of_deepArc_of_beta` leaves open on the
half-form route.

This is the composition the lane wants: when the two residuals are proved at the
family's own constant, this loses its hypotheses, `SharpGreendlingerGate`
becomes a theorem, and `GreendlingerFreeGate.torsionFree_of_sharpGate` and
`router_conclusions_of_sharpGate` deliver both router obligations with no
further work. -/
theorem sharpGreendlingerGate_of_deepArcSharp_of_betaSharp [DecidableEq α]
    (hdeep : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepArcSourceSharp R lam)
    (hbeta : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → LandingProductionBetaSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate α :=
  sharpGreendlingerGate_of_cascadeLandingSharp
    (cascadeLandingSharp_family_of_deepArcSharp_of_betaSharp hdeep hbeta)

/-- The same, on the router's own alphabet. -/
theorem sharpGreendlingerGate_fin_two_of_deepArcSharp_of_betaSharp
    (hdeep : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepArcSourceSharp R lam)
    (hbeta : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → LandingProductionBetaSharp R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) :=
  sharpGreendlingerGate_of_deepArcSharp_of_betaSharp hdeep hbeta

/-! ## 10.  The disjunctive landing obligation

`cascadeLandingSharp_of_deepArcSharp_of_landingSharp` commits to the *right*
disjunct of `CascadeLandingSharp` before it calls the landing hypothesis, which
throws the left one away: the located conclusion from the **head** factor is
unavailable to a landing prover, even though `CascadeLandingSharp` would have
accepted it.  That is not a cosmetic loss.

`Sofic.GreendlingerLandingProd` records where it bites.  At the adjacent factor
the intrusion is `|q| + |E|` --- the head conjugator's overhang past the landing
conjugator, plus the relator segment it eats --- and the (α) site is unavailable
exactly when `q ≠ []`, so the residual regime *is* the nonempty-overhang regime.
There the minimality move gives `2|q| ≤ |t'|` and the metric condition gives
`|E| < λ·|t'|`, so together only `|q| + |E| < (1/2 + λ)·|t'|`, where the offset
field of `LandsInSharp` needs `|q| + |E| < λ·|t'|`.  The whole shortfall is the
overhang; `q` is a conjugator segment and no piece bound controls a conjugator
segment; and sharpening `λ` makes the ratio `(1/2 + λ)/λ` worse, not better.  At
a one-factor tail this is an outright falsification handle
(`ne_nil_of_landingProductionBetaSharp`), so `LandingProductionBetaSharp` as
stated is not merely hard --- it is very likely false.

But in exactly that configuration the head factor keeps enough.  The block stops
past the adjacent conjugator, so what survives of `t` stands at position `|c|`
and exceeds `(1 − λ)|t|`, which `greendlingerAtSharp_of_bounded_cancellation`
accepts.  So the repair is not to weaken the landing site: it is to stop
discarding the disjunct that configuration lands in.

The primed predicates below are the unprimed ones with the conclusion widened to
`CascadeLandingSharp`'s own disjunction, and the primed assembly passes that
disjunction through instead of pre-committing.  Nothing else moves --- the
hypothesis lists are identical and the `λ`-free (α) plumbing is consumed exactly
as before --- and `landingProductionSharp'_of_landingProductionSharp` says the
unprimed form still discharges the primed one, so a prover who *can* produce a
landing site outright loses nothing by the change.
-/

/-- **The landing obligation, disjunctive.**  `LandingProductionSharp` with the
conclusion widened to the disjunction `CascadeLandingSharp` actually states: the
landing prover may answer with the head factor's located subword instead of a
landing site. -/
def LandingProductionSharp' [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (j : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (j : ℚ) < lam * (t.length : ℚ) →
    M.length + j ≤ c.length + t.length →
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') ∨
      LandsInSharp R lam M.length (conjEval e).toWord e.length

/-- **The landing obligation, (β) only, disjunctive.**  The residual the lane
should actually be proving: same hypothesis list as
`LandingProductionBetaSharp`, same orientation package, same exclusion of the
conjugator-absorbed regime, and the conclusion the assembly can genuinely
use. -/
def LandingProductionBetaSharp' [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' E : List (α × Bool)) (j : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (j : ℚ) < lam * (t.length : ℚ) →
    M.length + j ≤ c.length + t.length →
    M = E ++ FreeGroup.invRev c →
    FreeGroup.invRev M = c ++ FreeGroup.invRev E →
    E <:+ t → 0 < E.length →
    ¬ConjugatorAbsorbedSite c E M e →
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') ∨
      LandsInSharp R lam M.length (conjEval e).toWord e.length

/-- The unprimed obligation discharges the primed one: a landing site is one of
the two answers.  Kept so that the change costs no existing work --- anything
proved against `LandingProductionSharp` still feeds the new assembly. -/
theorem landingProductionSharp'_of_landingProductionSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (h : LandingProductionSharp R lam) :
    LandingProductionSharp' R lam :=
  fun c t e g P' M B' j hmin ht hredp heq htail hlow hj hle =>
    Or.inr (h c t e g P' M B' j hmin ht hredp heq htail hlow hj hle)

/-- The same, on the (β) side. -/
theorem landingProductionBetaSharp'_of_landingProductionBetaSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (h : LandingProductionBetaSharp R lam) : LandingProductionBetaSharp' R lam :=
  fun c t e g P' M B' E j hmin ht hredp heq htail hlow hj hle hM hMinv hEt
    hEpos hsite =>
    Or.inr (h c t e g P' M B' E j hmin ht hredp heq htail hlow hj hle hM hMinv
      hEt hEpos hsite)

/-- **The landing production with case (α) discharged, disjunctive.**  The
`λ`-free plumbing of `Sofic.GreendlingerAlphaPlumb` is consumed exactly as in
`landingProductionSharp_of_betaSharp`; the (α) branch answers with a landing
site, and the (β) branch passes the residual's disjunction through. -/
theorem landingProductionSharp'_of_betaSharp' [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    (hbeta : LandingProductionBetaSharp' R lam) :
    LandingProductionSharp' R lam := by
  intro c t e g P' M B' j hmin ht hredp heq htail hlow hj hle
  obtain ⟨E, hM, hMinv, hEt, -, hEpos⟩ :=
    eaten_prefix_orientation heq hlow (by omega)
  by_cases hsite : ConjugatorAbsorbedSite c E M e
  · exact Or.inr (landsInSharp_of_conjugatorAbsorbedSite hmetric hmin ht hEt
      hsite)
  · exact hbeta c t e g P' M B' E j hmin ht hredp heq htail hlow hj hle hM hMinv
      hEt hEpos hsite

/-- **`CascadeLandingSharp` from the two obligations, without pre-committing.**
The repair: the regime inequality still decides which obligation is called, but
in the landing regime the answer is relayed to whichever disjunct it came back
in.  This is the only theorem in the chain that had to change. -/
theorem cascadeLandingSharp_of_deepArcSharp_of_landingSharp' [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hdeep : DeepArcSourceSharp R lam) (hland : LandingProductionSharp' R lam) :
    CascadeLandingSharp R lam := by
  intro c t e g P' M B' j hmin ht hredp heq htail hlow hj
  rcases le_or_gt (M.length + j) (c.length + t.length) with hle | hgt
  · rcases hland c t e g P' M B' j hmin ht hredp heq htail hlow hj hle with
      harc | hlands
    · exact Or.inl harc
    · exact Or.inr ⟨hle, hlands⟩
  · exact Or.inl (hdeep c t e g P' M B' j hmin ht hredp heq htail hlow hj hgt)

/-- **`CascadeLandingSharp` over the disjunctive (β)-side residual.** -/
theorem cascadeLandingSharp_of_deepArcSharp_of_betaSharp' [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepArcSourceSharp R lam)
    (hbeta : LandingProductionBetaSharp' R lam) :
    CascadeLandingSharp R lam :=
  cascadeLandingSharp_of_deepArcSharp_of_landingSharp' hdeep
    (landingProductionSharp'_of_betaSharp' hmetric hbeta)

/-- **The sharp conclusion over the disjunctive (β)-side residual.** -/
theorem greendlingerConclusionSharp_of_deepArcSharp_of_betaSharp'
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepArcSourceSharp R lam)
    (hbeta : LandingProductionBetaSharp' R lam) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_cascadeLandingSharp hR hRne hlam0 hlam
    (cascadeLandingSharp_of_deepArcSharp_of_betaSharp' hmetric hdeep hbeta)

/-- **The residual bundle over the disjunctive landing obligation**, in the
shape `sharpGreendlingerGate_of_cascadeLandingSharp` consumes.  The primed
analogue of `cascadeLandingSharp_family_of_deepArcSharp_of_betaSharp`, and the
one the lane should now aim at. -/
theorem cascadeLandingSharp_family_of_deepArcSharp_of_betaSharp'
    [DecidableEq α]
    (hdeep : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepArcSourceSharp R lam)
    (hbeta : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → LandingProductionBetaSharp' R lam) :
    ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → CascadeLandingSharp R lam :=
  fun R lam hcyc hRne hlam0 hlam hmetric =>
    cascadeLandingSharp_of_deepArcSharp_of_betaSharp' hmetric
      (hdeep R lam hcyc hRne hlam0 hlam hmetric)
      (hbeta R lam hcyc hRne hlam0 hlam hmetric)

/-- **The sharp gate over the disjunctive (β)-side residual.** -/
theorem sharpGreendlingerGate_of_deepArcSharp_of_betaSharp' [DecidableEq α]
    (hdeep : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepArcSourceSharp R lam)
    (hbeta : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → LandingProductionBetaSharp' R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate α :=
  sharpGreendlingerGate_of_cascadeLandingSharp
    (cascadeLandingSharp_family_of_deepArcSharp_of_betaSharp' hdeep hbeta)

end SmallCancellationRouter
end GroupApproximation
