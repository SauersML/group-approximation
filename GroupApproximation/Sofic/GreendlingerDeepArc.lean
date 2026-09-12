import GroupApproximation.Sofic.GreendlingerReducedness

/-!
# The deep arc: the head is gone, so the conclusion comes from the tail

`GreendlingerBetaBranch` splits `CascadeLanding` at one inequality.  On the
side `M.length + j ≤ c.length + t.length` the landing site itself serves, and
`GreendlingerDeepestMatch` supplies it.  This file works the other side,
`DeepArcSource`: the **deep regime**, where the block the head factor loses runs
so far that the head's own survivor cannot carry the located conclusion.

## What "deep" means quantitatively

The regime hypotheses are `6 * j < t.length` and
`c.length + t.length < M.length + j`.  Writing `M = E ++ invRev c` for the
eaten stretch `E` of the head rotation, the two together give

    5 * t.length < 6 * E.length            (`five_mul_lt_six_mul_eaten`)

— the block eats **more than five sixths** of the head rotation.  That single
inequality is the engine of the whole file, because `C'(1/6)` bounds a piece by
one sixth and `5/6 > 1/6`.  Everything below is a reading of that gap.

## The rigidity the gap buys

`eq_of_sixth_common_prefix` is the general form: a word that prefixes two
symmetrized relators and occupies at least a **sixth** of the first forces the
two relators to be equal, since otherwise it is a piece and `C'(1/6)` refutes
its length.  In the deep regime the eaten segment occupies five sixths, so
wherever `invRev E` reappears among relator letters, the relator it lands in
*is* the head relator, rotated.  That is `eq_rotate_of_deep_intrusion`, and it
turns three separate configurations into three coincidences, each already
refutable:

* `not_deep_intrusion_of_reduced` — the (β) shape, where the head conjugator's
  last `i` letters align against the landing rotation.  The coincidence is void
  by `GreendlingerReducedness.invRev_ne_rotate_of_isReduced`, which spends
  nothing but reducedness of the head palindrome, so this kill works at **any**
  depth of the cascade, adjacent or not.
* `not_deep_hug_adjacent` — the head conjugator overhangs the next one by `q`
  and the segment lands `q` letters into the next rotation.  The coincidence
  makes the two adjacent factors mutually inverse
  (`mk_palindrome_mul_eq_one_of_coincidence`), which minimality forbids.
* `not_deep_overhang_adjacent` — the mirror, where the *next* conjugator
  overhangs by the inverse of a trailing block `E₂` of the eaten stretch and the
  rest `E₁` of it prefixes the next rotation.  Same argument through
  `mk_palindrome_mul_eq_one_of_coincidence'`.  Here the threshold spent is the
  sixth and not the five sixths, because `E₁` is only part of the eaten stretch.

## The half-pin closes the remaining adjacent shape

If the eaten stretch is not matched against relator letters at all, it is buried
in the next conjugator — `c' = c ++ (invRev E ++ Z)` — and that is exactly the
configuration of `two_mul_eaten_le_of_minimal_reroute`, which pins the eaten
stretch at half the rotation.  Half against five sixths is a contradiction:
`not_deep_eaten_buried`.

So at the adjacent junction the deep regime survives only where the eaten
stretch runs past the next rotation into that factor's **trailing** conjugator,
or past the next palindrome altogether.  Both are cascade shapes, not junction
shapes, and neither is settled here.

## What is left, and where it plugs in

`DeepTailArc` is the residual, and it is stated on the tail word alone: all of
the head-side bookkeeping — the length of the survivor `P'`, the position
arithmetic, the prepending — is discharged by `deepArcSource_of_deepTailArc`,
and `deepTailArc_of_deepArcSource` proves the converse, so the isolation loses
nothing at all.  The residual asks only this: the part of the tail word that
survives the head's cancellation carries a located Greendlinger arc, beginning
at or after the depth `M.length + j - (c.length + t.length)` by which the block
overran.

Two producers are provided for that arc, matching the two sources the design
note names: `greendlingerAt_of_untouched_rotation`, for a later factor whose
rotation the cascade never touched, and `greendlingerAt_of_deep_arc`, for the
reappearance copy of `GreendlingerBetaBranch.palindrome_eq_append_reappearance`
— the deep eaten stretch is itself more than half of a rotation of the head
relator, so a copy of it anywhere in the surviving word *is* the conclusion.
`exists_deep_tail_setup` puts the tail into palindromic normal form so that the
junction analysis of the previous section can be run on it.

Depends on `C'(1/6)` exactly where the piece bound is read, and on minimality
exactly where a coincidence is refuted.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The arithmetic of the deep regime -/

/-- The length of a palindrome, named so the position bookkeeping below can
cite it rather than unfolding. -/
theorem length_palindrome (c t : List (α × Bool)) :
    (palindrome c t).length = c.length + t.length + c.length := by
  unfold palindrome
  rw [List.length_append, List.length_append, FreeGroup.invRev_length]

/-- **The deep regime eats five sixths of the head rotation.**  The offset `j`
is below a sixth of the rotation and the block overruns by `j`, so what it eats
past the trailing conjugator exceeds `5/6` of the rotation.

This is the only place the two regime inequalities are combined, and every kill
below reads off this one number. -/
theorem five_mul_lt_six_mul_eaten {c t M E : List (α × Bool)} {j : ℕ}
    (hM : M = E ++ FreeGroup.invRev c)
    (hj : 6 * j < t.length)
    (hgt : c.length + t.length < M.length + j) :
    5 * t.length < 6 * E.length := by
  have hMlen : M.length = E.length + c.length := by
    rw [hM, List.length_append, FreeGroup.invRev_length]
  omega

/-- Five sixths is in particular a sixth: the weakening the rigidity lemmas
consume. -/
theorem length_le_six_mul_of_deep {t E : List (α × Bool)}
    (h : 5 * t.length < 6 * E.length) : t.length ≤ 6 * E.length := by
  omega

/-- **The tail of a deep configuration is nonempty.**  A cancellation reaching
past the trailing conjugator destroys a nonempty block, and the empty
expression spells the identity, whose reduced word destroys nothing.

Recorded because it is the first case split any analysis of `DeepArcSource`
makes, and because it needs no hypothesis beyond the block being long. -/
theorem tail_ne_nil_of_cancellation [DecidableEq α]
    {c M B' : List (α × Bool)} {e : List (FreeGroup α × List (α × Bool))}
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) : e ≠ [] := by
  rintro rfl
  have hnil : FreeGroup.invRev M ++ B' = [] := by
    rw [← htail, conjEval_nil]
    exact FreeGroup.toWord_eq_nil_iff.mpr rfl
  have hz := congrArg List.length hnil
  rw [List.length_append, FreeGroup.invRev_length, List.length_nil] at hz
  omega

/-! ## 2.  Producing the located conclusion -/

/-- Prepending a block to a word moves a located arc later by the block's
length.  The trivial direction of the position bookkeeping, and the one the
deep reduction spends. -/
theorem GreendlingerAt.append_left {R : Set (List (α × Bool))} {n : ℕ}
    {V : List (α × Bool)} (h : GreendlingerAt R n V) (P : List (α × Bool)) :
    GreendlingerAt R (P.length + n) (P ++ V) := by
  obtain ⟨A, u, C, hV, hlen, s, hs, hupre, hlt⟩ := h
  refine ⟨P ++ A, u, C, ?_, ?_, s, hs, hupre, hlt⟩
  · rw [hV]
    simp only [List.append_assoc]
  · rw [List.length_append]
    omega

/-- **An untouched rotation is an arc.**  A whole symmetrized relator sitting in
the word at or after position `n` gives the located conclusion outright: a
nonempty word is more than half of itself.

This is the first of the two sources the deep regime can draw on — a later
factor the cascade never reached. -/
theorem greendlingerAt_of_untouched_rotation {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) {s w A C : List (α × Bool)} {n : ℕ}
    (hs : s ∈ symmetrization R) (hw : w = A ++ s ++ C) (hn : n ≤ A.length) :
    GreendlingerAt R n w := by
  refine ⟨A, s, C, hw, hn, s, hs, List.prefix_refl s, ?_⟩
  have hpos : 0 < s.length :=
    List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne hs)
  omega

/-- **The eaten stretch is itself an arc.**  A suffix of a rotation occupying
more than half of it prefixes another rotation of the same relator, so a copy of
it anywhere in the word at or after position `n` gives the located conclusion.

This is the second source: the reappearance copy of
`GreendlingerBetaBranch.palindrome_eq_append_reappearance`.  In the deep regime
the hypothesis `t.length < 2 * E.length` is free — `five_mul_lt_six_mul_eaten`
gives five sixths, and five sixths is more than a half — so the reappearance
copy of a deep block always closes the goal wherever it lands late enough. -/
theorem greendlingerAt_of_deep_arc {R : Set (List (α × Bool))}
    {t E w A C : List (α × Bool)} {n : ℕ}
    (ht : t ∈ symmetrization R) (hEt : E <:+ t)
    (hhalf : t.length < 2 * E.length)
    (hw : w = A ++ E ++ C) (hn : n ≤ A.length) :
    GreendlingerAt R n w := by
  obtain ⟨z, hz⟩ := hEt
  have hrot : t.rotate z.length = E ++ z := by
    rw [← hz]
    exact rotate_append z E
  refine ⟨A, E, C, hw, hn, t.rotate z.length,
    rotate_mem_symmetrization ht z.length, ?_, ?_⟩
  · rw [hrot]
    exact ⟨z, rfl⟩
  · rw [List.length_rotate]
    exact hhalf

/-! ## 3.  Rigidity: a long common prefix identifies the two relators -/

/-- **A sixth is already rigid.**  A word prefixing two symmetrized relators and
occupying at least a sixth of the first is not a piece, so under `C'(1/6)` the
two relators coincide.

Everything the deep regime does to a junction goes through this statement: the
regime makes the eaten stretch five sixths of its rotation, five sixths is at
least a sixth, and so every occurrence of that stretch among relator letters is
an occurrence of the head relator itself. -/
theorem eq_of_sixth_common_prefix {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {p s s' : List (α × Bool)}
    (hs : s ∈ symmetrization R) (hs' : s' ∈ symmetrization R)
    (hps : p <+: s) (hps' : p <+: s')
    (hlong : s.length ≤ 6 * p.length) : s = s' := by
  by_contra hne
  have hpiece : IsPiece (symmetrization R) p :=
    isPiece_of_prefix_two hs hs' hne hps hps'
  have h6 := six_mul_length_lt_of_isPiece hmetric hpiece hs hps
  omega

/-- **The intrusion lands in the head relator.**  An eaten stretch occupying at
least a sixth of the rotation it came out of, prefixing a rotation of a
symmetrized relator, forces that rotation to be the inverted head rotation.

Stated as an equation rather than as a refuted piece because that is the shape
the three coincidence lemmas consume. -/
theorem eq_rotate_of_deep_intrusion {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {t t' E : List (α × Bool)} {k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hEt : E <:+ t) (hlong : t.length ≤ 6 * E.length)
    (hintr : FreeGroup.invRev E <+: t'.rotate k) :
    FreeGroup.invRev t = t'.rotate k := by
  refine eq_of_sixth_common_prefix hmetric (invRev_mem_symmetrization ht)
    (rotate_mem_symmetrization ht' k) (invRev_prefix_of_suffix hEt) hintr ?_
  rw [FreeGroup.invRev_length, FreeGroup.invRev_length]
  exact hlong

/-- The same, read straight off the regime hypotheses of `DeepArcSource`. -/
theorem eq_rotate_of_deep_eaten {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {c t t' M E : List (α × Bool)} {j k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hM : M = E ++ FreeGroup.invRev c) (hEt : E <:+ t)
    (hj : 6 * j < t.length)
    (hgt : c.length + t.length < M.length + j)
    (hintr : FreeGroup.invRev E <+: t'.rotate k) :
    FreeGroup.invRev t = t'.rotate k :=
  eq_rotate_of_deep_intrusion hmetric ht ht' hEt
    (length_le_six_mul_of_deep (five_mul_lt_six_mul_eaten hM hj hgt)) hintr

/-! ## 4.  The three coincidences the rigidity produces are all refuted -/

/-- **The (β) intrusion is impossible, at any depth.**  If the head conjugator's
last `i` letters align against `t'.rotate k` and the eaten stretch follows them
into `t'.rotate (k + i)`, rigidity makes that rotation the inverted head
rotation — and `GreendlingerReducedness.invRev_ne_rotate_of_isReduced` says it
is not, on reducedness of the head palindrome alone.

No minimality and no adjacency: this refutation applies to a landing factor
anywhere in the cascade, which is what makes it the deep regime's main tool. -/
theorem not_deep_intrusion_of_reduced [DecidableEq α]
    {R : Set (List (α × Bool))} (hmetric : MetricSmallCancellation R (1 / 6))
    {c t t' E : List (α × Bool)} {i k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hpal : FreeGroup.IsReduced (palindrome c t))
    (hEt : E <:+ t) (hlong : t.length ≤ 6 * E.length)
    (hi : 0 < i) (hic : i ≤ c.length)
    (halign : c.drop (c.length - i) <+: t'.rotate k)
    (hintr : FreeGroup.invRev E <+: t'.rotate (k + i)) : False :=
  invRev_ne_rotate_of_isReduced hpal hi hic halign
    (eq_rotate_of_deep_intrusion hmetric ht ht' hEt hlong hintr)

/-- **The hug intrusion is impossible.**  The head conjugator overhangs the next
one by `q`, a prefix of the next rotation, and the eaten stretch lands `q`
letters in.  Rigidity turns that into the coincidence
`invRev t = t'.rotate q.length`, which makes the two adjacent factors mutually
inverse; a minimal expression has no such pair. -/
theorem not_deep_hug_adjacent [DecidableEq α] {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {c c' q t t' E : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hEt : E <:+ t) (hlong : t.length ≤ 6 * E.length)
    (hcq : c = c' ++ q) (hqt : q <+: t')
    (hintr : FreeGroup.invRev E <+: t'.rotate q.length) : False :=
  mk_palindrome_mul_ne_one_of_minimal hmin
    (mk_palindrome_mul_eq_one_of_coincidence hcq hqt
      (eq_rotate_of_deep_intrusion hmetric ht ht' hEt hlong hintr))

/-- **The overhang intrusion is impossible.**  The mirror configuration: the
next conjugator is the head conjugator followed by the inverse of a trailing
block `E₂` of the eaten stretch, and what is left of the stretch prefixes the
next rotation.  Rigidity identifies that rotation with a rotation of the
inverted head rotation, and
`GreendlingerOverlap.mk_palindrome_mul_eq_one_of_coincidence'` turns the
identification into a cancelling pair.

The bound spent here is the sixth and not the five sixths, because `E₁` is only
the part of the eaten stretch that escapes the conjugator; the deep regime
supplies five sixths for the whole stretch and the caller must account for the
buried part separately, which is what `not_deep_eaten_buried` is for. -/
theorem not_deep_overhang_adjacent [DecidableEq α] {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {c t t' E₁ E₂ : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t)
        :: (FreeGroup.mk (c ++ FreeGroup.invRev E₂), t') :: e) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hEt : E₁ ++ E₂ <:+ t) (hlong : t.length ≤ 6 * E₁.length)
    (hintr : FreeGroup.invRev E₁ <+: t') : False := by
  have hpre : FreeGroup.invRev E₂ ++ FreeGroup.invRev E₁
      <+: FreeGroup.invRev t := by
    have h := invRev_prefix_of_suffix hEt
    rwa [FreeGroup.invRev_append] at h
  have hy : FreeGroup.invRev E₂ <+: FreeGroup.invRev t :=
    (show FreeGroup.invRev E₂ <+: FreeGroup.invRev E₂ ++ FreeGroup.invRev E₁
      from ⟨FreeGroup.invRev E₁, rfl⟩).trans hpre
  have hrot : FreeGroup.invRev E₁
      <+: (FreeGroup.invRev t).rotate (FreeGroup.invRev E₂).length :=
    prefix_rotate_of_append_prefix hpre
  have heq : (FreeGroup.invRev t).rotate (FreeGroup.invRev E₂).length = t' := by
    refine eq_of_sixth_common_prefix hmetric
      (rotate_mem_symmetrization (invRev_mem_symmetrization ht)
        (FreeGroup.invRev E₂).length) ht' hrot hintr ?_
    rw [List.length_rotate, FreeGroup.invRev_length, FreeGroup.invRev_length]
    exact hlong
  exact mk_palindrome_mul_ne_one_of_minimal hmin
    (mk_palindrome_mul_eq_one_of_coincidence'
      (y := FreeGroup.invRev E₂) rfl hy heq.symm)

/-- **A deep block cannot be buried in the next conjugator.**  If the whole
eaten stretch is absorbed by the next conjugator, the reroute of
`GreendlingerBetaBranch.two_mul_eaten_le_of_minimal_reroute` pins it at half the
rotation, and the deep regime puts it above five sixths.

This is the one configuration in the adjacent junction analysis that carries no
relator letters at all, so rigidity has nothing to say about it and the weight
move has to do the work alone. -/
theorem not_deep_eaten_buried [DecidableEq α] {R : Set (List (α × Bool))}
    {c t₀ E Z m : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t₀ ++ E)
        :: (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)), m) :: e) g)
    (hred : FreeGroup.IsReduced (c ++ (FreeGroup.invRev E ++ Z)))
    (hredc : FreeGroup.IsReduced c)
    (hdeep : 5 * (t₀ ++ E).length < 6 * E.length) : False := by
  have h := two_mul_eaten_le_of_minimal_reroute hmin hred hredc
  rw [List.length_append] at h hdeep
  omega

/-! ## 5.  The tail, put in the shape the junction analysis reads -/

/-- **The deep configuration's tail, normalized.**  The tail of a deep
configuration is nonempty, and its leading factor may be replaced by its
palindromic normal form without touching the head factor or what the tail
spells.

This is the entry point for any analysis of `DeepTailArc`: it hands over the
adjacent junction — head palindrome `palindrome c t`, next palindrome
`palindrome c' t'` — that section 4 refutes case by case. -/
theorem exists_deep_tail_setup [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {c t M B' : List (α × Bool)} {e : List (FreeGroup α × List (α × Bool))}
    {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) :
    ∃ (c' t' : List (α × Bool)) (f : List (FreeGroup α × List (α × Bool))),
      t' ∈ symmetrization R ∧
        FreeGroup.IsReduced (palindrome c' t') ∧
        IsMinimalConjExpr R
          ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: f) g ∧
        conjEval ((FreeGroup.mk c', t') :: f) = conjEval e ∧
        f.length < e.length := by
  have hne := tail_ne_nil_of_cancellation htail hlow
  obtain ⟨x, f, rfl⟩ : ∃ x f, e = x :: f := by
    cases e with
    | nil => exact absurd rfl hne
    | cons x f => exact ⟨x, f, rfl⟩
  obtain ⟨x', s'⟩ := x
  obtain ⟨c', t', ht', hredp', hmin'⟩ := exists_palindromic_snd hR hRne hmin
  refine ⟨c', t', f, ht', hredp', hmin', ?_, ?_⟩
  · have h1 := hmin'.2.1
    have h2 := hmin.2.1
    rw [conjEval_cons] at h1 h2
    exact mul_left_cancel (h1.trans h2.symm)
  · rw [List.length_cons]
    omega

/-! ## 6.  The residual, and the reduction to it -/

/-- **What the deep regime still owes.**  The surviving part of the tail word
carries a located Greendlinger arc, beginning at or after the depth by which the
head's block overran its own palindrome.

Every quantifier is the one `DeepArcSource` has, with the head survivor `P'`
eliminated: the block is named only as a suffix of the head palindrome, and the
conclusion is located inside `B'` rather than inside `P' ++ B'`.  That is not a
weakening — `deepTailArc_of_deepArcSource` derives it back — it is the same
statement with the head-side arithmetic already done, which is what makes the
tail analysis of sections 4 and 5 applicable to it directly. -/
def DeepTailArc [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t M B' : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α) (j : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    M <:+ palindrome c t →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → 6 * j < t.length →
    c.length + t.length < M.length + j →
    GreendlingerAt R (M.length + j - (c.length + t.length)) B'

/-- **The deep obligation, from the tail obligation.**  Prepending the head
survivor moves the arc later by exactly `P'.length`, and in the deep regime
`P'.length + (M.length + j - (c.length + t.length))` is exactly `c.length + j`
— the head survivor and the overrun depth partition the required offset. -/
theorem deepArcSource_of_deepTailArc [DecidableEq α]
    {R : Set (List (α × Bool))} (h : DeepTailArc R) : DeepArcSource R := by
  intro c t e g P' M B' j hmin ht hredp heq htail hlow hj hgt
  have hlenP : P'.length + M.length = c.length + t.length + c.length := by
    have hb := congrArg List.length heq
    rw [List.length_append, length_palindrome] at hb
    exact hb.symm
  have harc :=
    h c t M B' e g j hmin ht hredp ⟨P', heq.symm⟩ htail hlow hj hgt
  refine (harc.append_left P').mono ?_
  omega

/-- **And conversely**, so the isolation is exact.  In the deep regime the head
survivor is strictly shorter than the required offset, so any arc `DeepArcSource`
produces begins strictly inside the tail survivor, and reading it there is the
tail obligation. -/
theorem deepTailArc_of_deepArcSource [DecidableEq α]
    {R : Set (List (α × Bool))} (h : DeepArcSource R) : DeepTailArc R := by
  intro c t M B' e g j hmin ht hredp hMsuf htail hlow hj hgt
  obtain ⟨P', hP'⟩ := hMsuf
  have hlenP : P'.length + M.length = c.length + t.length + c.length := by
    have hb := congrArg List.length hP'
    rw [List.length_append, length_palindrome] at hb
    exact hb
  obtain ⟨A, u, C, hw, hAlen, s, hs, hupre, hlt⟩ :=
    h c t e g P' M B' j hmin ht hredp hP'.symm htail hlow hj hgt
  have hPpre : P' <+: P' ++ B' := ⟨B', rfl⟩
  have hApre : A <+: P' ++ B' :=
    ⟨u ++ C, by rw [hw]; simp only [List.append_assoc]⟩
  obtain ⟨A₂, hA₂⟩ := List.prefix_of_prefix_length_le hPpre hApre (by omega)
  have hA₂len : P'.length + A₂.length = A.length := by
    have hb := congrArg List.length hA₂
    rw [List.length_append] at hb
    exact hb
  have hB' : B' = A₂ ++ u ++ C := by
    have hb : P' ++ B' = P' ++ (A₂ ++ u ++ C) := by
      rw [hw, ← hA₂]
      simp only [List.append_assoc]
    exact List.append_cancel_left hb
  exact ⟨A₂, u, C, hB', by omega, s, hs, hupre, hlt⟩

/-! ## 7.  The gate, through the residual -/

/-- `CascadeLanding` from the tail obligation and the landing production. -/
theorem cascadeLanding_of_deepTailArc_of_landing [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hdeep : DeepTailArc R) (hland : LandingProduction R) :
    CascadeLanding R :=
  cascadeLanding_of_deepArc_of_landing (deepArcSource_of_deepTailArc hdeep) hland

/-- **The free-group half-form gate, reduced to the tail obligation and the
landing production.**  Nothing else is assumed: the head-side arithmetic of the
deep regime is discharged, and what the deep branch still owes is a located arc
in the surviving tail word. -/
theorem greendlingerConclusion_of_deepTailArc_of_landing [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hdeep : DeepTailArc R) (hland : LandingProduction R) :
    GreendlingerConclusion R :=
  greendlingerConclusion_of_deepArc_of_landing hR hRne
    (deepArcSource_of_deepTailArc hdeep) hland

end SmallCancellationRouter
end GroupApproximation
