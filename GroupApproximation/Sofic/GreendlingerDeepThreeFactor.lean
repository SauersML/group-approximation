import GroupApproximation.Sofic.GreendlingerDeepVacuitySharp

/-!
# The three-factor overrun: the seed, and the one inequality it costs

`GreendlingerDeepVacuity` closes the deep regime at the adjacent junction and
leaves `DeepOverrunArc`, where the head's block runs past the whole adjacent
palindrome.  `not_deep_two_factor` settles two factors.  This file settles the
shape of the next case — three factors, the block overrunning the second and
landing in the third — and reduces it to a single arithmetic inequality.

The coordinator's structural finding is what fixes the method.  In the overrun
the landing factor's effective conjugator word **extends** the head conjugator
rather than being extended by it, so the coincidence lemmas' `c = d ++ q` is
unobtainable; and when the landing rotation does coincide, the cancelling pair
carries a *longer* conjugator, so removing it grows every factor in between and
minimality is not contradicted.  The coincidence may therefore be survivable
here.  Nothing in this file tries to refute the overrun — the conclusion is
**produced**.

## Where the arc has to come from, and why the reduction is sharp

At three factors the tail word is `palindrome c₂ t₂` glued to
`palindrome c₃ t₃`, and the overrun says the block covers the second factor's
survivor entirely.  `exists_three_factor_landing_drop` reads off what is left:

    B' = (palindrome c₃ t₃).drop N

for one number `N` — the total depth the block reached into the last palindrome.
So the surviving word is a suffix of a single palindrome, and the only
symmetrized relator occurring in it is `t₃`.  An arc must therefore lie inside
what `t₃` has left, and the window it has left, measured from the front of `B'`,
runs from `0` to `|t₃| − i` where `i = N − |c₃|` is the intrusion into the
rotation.  An arc must be longer than `|t₃| / 2` and must start at or after the
overrun depth `d`, so it fits exactly when

    2 · (i + d) < |t₃|.

That is both what `greendlingerAt_of_landing_drop` needs and — within `t₃`, the
only relator the configuration supplies — what any arc would need, so the
reduction below loses nothing that is not an accident of `invRev c₃` carrying
relator letters of its own.

## The sharp form is the `3λ` budget, exactly

`greendlingerAtSharp_of_landing_intrusion` is the same construction against the
sharp bound, and there the inequality reads

    (i + d : ℚ) < 3 · λ · |t₃|.

This is `GreendlingerSharpTwins.three_pieces_budget`'s right-hand side on the
nose: the sharp conclusion's whole allowance is `3λ` times the rotation, and in
the overrun the intrusion and the overrun depth are the two claims on it.  At
`λ = 1/6` it is `2(i + d) < |t₃|` again.

## What is left

`DeepOverrunDepth` — one inequality, carrying the whole three-factor
configuration as context so that every bound the count needs is in scope.  The
Chunks arithmetic is what should discharge it: `survivor_le_of_overrun` caps the
second factor's survivor at two thirds of `t₂` when the block overruns it, which
is what bounds `N` from below through `|P₂|`, and `survivor_gt_of_two_pieces`
pushes the other way, `not_consecutive_overrun` being the two together.  Those
are stated over abstract naturals, so feeding them here is a matter of naming
the segments, not of new geometry.

Nothing in this file is conditional on the count: the producers and the
decomposition are unconditional, and `DeepOverrunDepth` is named where the count
begins.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The arc a surviving rotation supplies -/

/-- **The landing arc.**  A rotation with `i` letters eaten off its front,
followed by anything, carries a located Greendlinger arc at every offset `d`
with `2(i + d) < |t₃|`: start the arc `d` letters into what survives and it is
still more than half of the rotation it came from.

This is `GreendlingerThreeFactor.greendlingerAt_of_bounded_cancellation` read at
the far end of the cascade rather than at the head — there the eaten stretch is
at the back of the rotation, here at the front — and it is the producer the
three-factor overrun needs, because at three factors the surviving word *is* a
suffix of the last palindrome. -/
theorem greendlingerAt_of_landing_intrusion {R : Set (List (α × Bool))}
    {t₃ Z : List (α × Bool)} {i d : ℕ}
    (ht₃ : t₃ ∈ symmetrization R)
    (hbound : 2 * (i + d) < t₃.length) :
    GreendlingerAt R d ((t₃ ++ Z).drop i) := by
  have hdrop : (t₃ ++ Z).drop i = t₃.drop i ++ Z :=
    drop_append_of_le i t₃ Z (by omega)
  refine ⟨(t₃.drop i).take d, (t₃.drop i).drop d, Z, ?_, ?_,
    t₃.rotate (i + d), rotate_mem_symmetrization ht₃ (i + d), ?_, ?_⟩
  · rw [hdrop, List.take_append_drop]
  · rw [List.length_take, List.length_drop]
    omega
  · have hu : (t₃.drop i).drop d = t₃.drop (i + d) := (drop_add i d t₃).symm
    rw [hu, List.rotate_eq_drop_append_take (show i + d ≤ t₃.length by omega)]
    exact ⟨t₃.take (i + d), rfl⟩
  · rw [List.length_rotate, List.length_drop, List.length_drop]
    omega

/-- **The landing arc, at the sharp constant.**  The same construction against
`(1 − 3λ)`, where the inequality becomes `i + d < 3λ·|t₃|` — the sharp
conclusion's entire allowance, claimed by the intrusion and the overrun depth
together. -/
theorem greendlingerAtSharp_of_landing_intrusion {R : Set (List (α × Bool))}
    {lam : ℚ} {t₃ Z : List (α × Bool)} {i d : ℕ}
    (ht₃ : t₃ ∈ symmetrization R)
    (hfit : i + d ≤ t₃.length)
    (hbound : (i : ℚ) + (d : ℚ) < 3 * lam * (t₃.length : ℚ)) :
    GreendlingerAtSharp R lam d ((t₃ ++ Z).drop i) := by
  have hle1 : i ≤ t₃.length := by omega
  have hle2 : d ≤ t₃.length - i := by omega
  have hdrop : (t₃ ++ Z).drop i = t₃.drop i ++ Z :=
    drop_append_of_le i t₃ Z hle1
  refine ⟨(t₃.drop i).take d, (t₃.drop i).drop d, Z, ?_, ?_,
    t₃.rotate (i + d), rotate_mem_symmetrization ht₃ (i + d), ?_, ?_⟩
  · rw [hdrop, List.take_append_drop]
  · rw [List.length_take, List.length_drop]
    omega
  · have hu : (t₃.drop i).drop d = t₃.drop (i + d) := (drop_add i d t₃).symm
    rw [hu, List.rotate_eq_drop_append_take (by omega : i + d ≤ t₃.length)]
    exact ⟨t₃.take (i + d), rfl⟩
  · rw [List.length_rotate, List.length_drop, List.length_drop]
    have hcast : ((t₃.length - i - d : ℕ) : ℚ)
        = (t₃.length : ℚ) - (i : ℚ) - (d : ℚ) := by
      rw [Nat.cast_sub hle2, Nat.cast_sub hle1]
    rw [hcast]
    linarith

/-- **The landing arc, read off a drop of the whole palindrome.**  The form the
three-factor decomposition produces: the surviving word is the last palindrome
with `N` letters removed, and the intrusion into its rotation is `N − |c₃|`.

Both regimes are covered.  When the block stops inside the last conjugator the
whole rotation survives and the bound reads `2d < |t₃|`; when it reaches past
it, the intrusion joins the overrun depth. -/
theorem greendlingerAt_of_landing_drop {R : Set (List (α × Bool))}
    {c₃ t₃ : List (α × Bool)} {N d : ℕ}
    (ht₃ : t₃ ∈ symmetrization R)
    (hbound : 2 * ((N - c₃.length) + d) < t₃.length) :
    GreendlingerAt R d ((palindrome c₃ t₃).drop N) := by
  have hP : palindrome c₃ t₃ = c₃ ++ (t₃ ++ FreeGroup.invRev c₃) := by
    unfold palindrome
    rw [List.append_assoc]
  rcases le_or_gt c₃.length N with hle | hgt
  · have hdrop : (palindrome c₃ t₃).drop N
        = (t₃ ++ FreeGroup.invRev c₃).drop (N - c₃.length) := by
      rw [hP, drop_append_of_ge c₃ N _ hle]
    rw [hdrop]
    exact greendlingerAt_of_landing_intrusion ht₃ hbound
  · have hdrop : (palindrome c₃ t₃).drop N
        = c₃.drop N ++ (t₃ ++ FreeGroup.invRev c₃).drop 0 := by
      rw [hP, drop_append_of_le N c₃ _ hgt.le, List.drop_zero]
    rw [hdrop]
    refine ((greendlingerAt_of_landing_intrusion (i := 0) ht₃
      (by omega)).append_left (c₃.drop N)).mono ?_
    omega

/-- **The count, split in two.**  The single inequality
`2(i + d) < |t₃|` follows from two independent ones: the intrusion into the
landing rotation is a piece, and the head's overrun depth is under a third of
that rotation.

This is the form to aim the count at, because the two halves are bounded by
different machinery — the first by `C'(1/6)` through the rigidity core of
`GreendlingerDeepArc`, the second by whatever bounds how far a head block may
outrun its own palindrome.  At the sharp constant the same split reads
`i < λ|t₃|` and `d < 2λ|t₃|`, whose sum is exactly the `3λ` allowance. -/
theorem greendlingerAt_of_piece_intrusion {R : Set (List (α × Bool))}
    {c₃ t₃ : List (α × Bool)} {N d : ℕ}
    (ht₃ : t₃ ∈ symmetrization R)
    (hi : 6 * (N - c₃.length) < t₃.length)
    (hd : 3 * d < t₃.length) :
    GreendlingerAt R d ((palindrome c₃ t₃).drop N) :=
  greendlingerAt_of_landing_drop ht₃ (by omega)

/-! ## 2.  What the overrun leaves at three factors -/

/-- **The three-factor overrun, decomposed.**  When the head's block covers the
second factor's survivor entirely, what is left of the tail word is a suffix of
the *third* palindrome — one drop, by one number.

The number is `|M₂| + (|M| − |P₂|)`: the depth the second factor's own block
reached plus the extra the head's block ran past it.  The proof is two
applications of the cancellation decomposition and one composition of drops; the
overrun hypothesis enters only to put `|P₂| ≤ |M|`, which is what makes the
second factor drop out of the picture entirely. -/
theorem exists_three_factor_landing_drop [DecidableEq α]
    {c₂ t₂ c₃ t₃ M B' : List (α × Bool)}
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (hredp₃ : FreeGroup.IsReduced (palindrome c₃ t₃))
    (htail : (conjEval ((FreeGroup.mk c₂, t₂)
        :: [(FreeGroup.mk c₃, t₃)])).toWord = FreeGroup.invRev M ++ B')
    (hover : ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂)) :
    ∃ N : ℕ, B' = (palindrome c₃ t₃).drop N := by
  have heval : conjEval ((FreeGroup.mk c₂, t₂) :: [(FreeGroup.mk c₃, t₃)])
      = FreeGroup.mk ((conjEval ((FreeGroup.mk c₂, t₂)
        :: [(FreeGroup.mk c₃, t₃)])).toWord) := (FreeGroup.mk_toWord).symm
  obtain ⟨P₂, M₂, B₂, heq₂, hgw₂, hwe₂⟩ :=
    exists_leading_cancellation FreeGroup.isReduced_toWord hredp₂ heval
  -- the last factor spells its own palindrome
  have hev₃ : conjEval [(FreeGroup.mk c₃, t₃)]
      = FreeGroup.mk (palindrome c₃ t₃) := by
    rw [conjEval_cons, conjEval_nil, mul_one, mk_palindrome]
  have hword₃ : (conjEval [(FreeGroup.mk c₃, t₃)]).toWord
      = palindrome c₃ t₃ := by
    rw [hev₃, FreeGroup.toWord_mk, hredp₃.reduce_eq]
  rw [hword₃] at hgw₂
  -- what the second factor's block leaves of the third palindrome
  have hB₂ : B₂ = (palindrome c₃ t₃).drop M₂.length := by
    rw [hgw₂, drop_append_of_ge (FreeGroup.invRev M₂) M₂.length B₂
      (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
      Nat.sub_self, List.drop_zero]
  -- the overrun says the second factor's survivor is inside the block
  rcases le_or_gt P₂.length M.length with hlen | hgt
  · have hkey : B' = B₂.drop (M.length - P₂.length) := by
      have h1 : FreeGroup.invRev M ++ B' = P₂ ++ B₂ := by
        rw [← htail, hwe₂]
      have h2 : (FreeGroup.invRev M ++ B').drop M.length = B' := by
        rw [drop_append_of_ge (FreeGroup.invRev M) M.length B'
          (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
          Nat.sub_self, List.drop_zero]
      rw [← h2, h1, drop_append_of_ge P₂ M.length B₂ hlen]
    refine ⟨M₂.length + (M.length - P₂.length), ?_⟩
    rw [hkey, hB₂, drop_add M₂.length (M.length - P₂.length)
      (palindrome c₃ t₃)]
  · exfalso
    refine hover ?_
    have hMpre : FreeGroup.invRev M
        <+: (conjEval ((FreeGroup.mk c₂, t₂)
          :: [(FreeGroup.mk c₃, t₃)])).toWord := ⟨B', htail.symm⟩
    have hP₂pre : P₂ <+: (conjEval ((FreeGroup.mk c₂, t₂)
        :: [(FreeGroup.mk c₃, t₃)])).toWord := ⟨B₂, hwe₂.symm⟩
    refine (List.prefix_of_prefix_length_le hMpre hP₂pre ?_).trans
      ⟨M₂, heq₂.symm⟩
    rw [FreeGroup.invRev_length]
    omega

/-! ## 3.  The count, isolated -/

/-- **The three-factor overrun count.**  One inequality: the intrusion into the
last rotation plus the depth by which the head's block overran its own
palindrome is under half of that rotation.

Every field of the configuration is carried so that the count has its context:
minimality of the whole expression, the three rotations, the two reducedness
facts, the block, the overrun, and the drop position `N` that
`exists_three_factor_landing_drop` produces.

`GreendlingerChunks.survivor_le_of_overrun`,
`GreendlingerChunks.survivor_gt_of_two_pieces` and
`GreendlingerChunks.not_consecutive_overrun` are stated over abstract naturals
and are what this should be discharged against; the work is to name the segments
the count runs over, not to find new geometry. -/
def DeepOverrunDepth [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
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
    c.length < M.length → 6 * j < t.length →
    c.length + t.length < M.length + j →
    2 * ((N - c₃.length) + (M.length + j - (c.length + t.length)))
      < t₃.length

/-- **The three-factor overrun case, from the count.**  This is the conclusion
`DeepOverrunArc` asks for, at the instance where the tail has exactly two
factors — the induction seed above `not_deep_two_factor`.

The decomposition and the producer are unconditional; `DeepOverrunDepth` is the
whole of what is assumed. -/
theorem greendlingerAt_of_deepOverrunDepth [DecidableEq α]
    {R : Set (List (α × Bool))} (h : DeepOverrunDepth R)
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
    (hlow : c.length < M.length) (hj : 6 * j < t.length)
    (hgt : c.length + t.length < M.length + j) :
    GreendlingerAt R (M.length + j - (c.length + t.length)) B' := by
  obtain ⟨N, hB'⟩ :=
    exists_three_factor_landing_drop hredp₂ hredp₃ htail hover
  rw [hB']
  exact greendlingerAt_of_landing_drop ht₃
    (h c t c₂ t₂ c₃ t₃ M B' g j N hmin ht ht₂ ht₃ hredp hredp₂ hredp₃ hMsuf
      htail hover hB' hlow hj hgt)

end SmallCancellationRouter
end GroupApproximation
