import GroupApproximation.Sofic.GreendlingerEmptyConjCorner
import GroupApproximation.Sofic.GreendlingerInduction

/-!
# The empty-conjugator corner does not descend on factor count

`GreendlingerEmptyConjCorner.noDeepCollapseEmptyConj_of_greendlingerConclusion`
reduces the last deep gap `NoDeepCollapseEmptyConj` to the **half-form**
`GreendlingerConclusion`, and its own docstring records that the reduction is
circular as stated: the routing lane consumes `DeepCompositeLandsSharp` on its
way to `GreendlingerConclusionSharp`.  The natural repair is an induction on
factor count -- discharge the corner at count `n` from the conclusion at counts
`< n`, which the lane's own induction (`GreendlingerDeepInvariant`,
`greendlingerAtSharp_drop_of_lands`) already has in hand.

This file settles whether that repair is available.  It is not, and the two
lemmas that say so are `emptyConj_survivor_count` and `emptyConj_word_eq`.

## 1.  The corner's Greendlinger demand sits at the ambient count

In a collapsed configuration `g = FreeGroup.mk P'` (`mk_eq_of_collapse`), and
`(mk c, t) :: e` is a *minimal* expression for `g`, so
`isMinimalConjProduct_of_isMinimalConjExpr` gives

    `IsMinimalConjProduct R (e.length + 1) (FreeGroup.mk P')`

-- `emptyConj_survivor_count`.  The word `P'` the reduction feeds to
`GreendlingerConclusion` therefore has minimal factor count **exactly the count
of the configuration it came from**, not one less.  Worse, `emptyConj_word_eq`:
whenever the ambient reduced word `w` spells `g` -- which is how
`greendlingerAtSharp_drop_of_lands` carries it -- `w = P'` on the nose.  So the
input consumed at the leaf is the conclusion *for the very word, at the very
count*, that the induction step is trying to produce.  There is no descent.

## 2.  The object that does descend carries no information

What the collapse does expose one factor lower is the block `M`:
`isMinimalConjExpr_tail_of_collapse` makes `e` minimal for `(mk M)⁻¹`, so

    `IsMinimalConjProduct R e.length (FreeGroup.mk M)`

-- `emptyConj_tail_block_data`, together with `M ≠ []`, `M` reduced, and
`mk M` in the normal closure.  That is a genuine drop from `e.length + 1` to
`e.length`.  But the half-form conclusion at `M` is *satisfied outright*:
`t = P' ++ M` with `|P'| < lam·|t| ≤ |t|/2`, so the rotation `M ++ P'` is a
symmetrized relator having `M` itself as a prefix and `|M ++ P'| = |t| < 2|M|`.
`greendlingerConclusion_holds_for_tail_block` exhibits that witness.  No
contradiction can be extracted at the lower count from the half-form, and this
is a theorem, not an observation about a failed attempt.

**Verdict: induction on factor count does not break the circle.**  The corner is
not "the conclusion at smaller counts"; it is the conclusion at its own count,
on its own word.

## 3.  What a lower-count input would have to say

The half-form fails at `M` because one long arc inside `M` is free -- the
rotation of `t`.  *Two* arcs are not: `length_eq_of_long_arc` says any subword of
a symmetrized relator that is more than half of a symmetrized relator forces the
two relators to have equal length, so each such arc inside `M` is longer than
`|t|/2`, and two of them do not fit inside `M`, which is shorter than `t`.

`DisjointArcBudget` isolates exactly the hypothesis that argument uses: two arcs
inside the word whose lengths *sum to at most the word's length*.  It does not
ask them to be consecutive, or ordered, or separated -- only budgeted.
`not_disjointArcBudget_of_relator_suffix` refutes it for a proper suffix of a
symmetrized relator, and `tail_ne_nil_of_arcBudgetBelow` closes the corner at
count `n` from that hypothesis at counts `< n`.  `ArcBudgetBelow` is the graded
form, so the consumption really is strictly below the ambient count.

**This is a conditional route and it is not progress.**  `DisjointArcBudget` is
weaker than `GreendlingerInduction.TwoPieceConclusion`
(`disjointArcBudget_of_twoPieceConclusion`), and `TwoPieceConclusion` is
*false* in general -- `GreendlingerTwoPieceRegime` carries the counterexample and
the cyclic statement that replaces it.  What is recorded here is only the
*location* of the demand: the two-arc input is consumed one factor below the
ambient count, which is what the half-form input is not.  Whether the cyclic
Greendlinger statement implies `DisjointArcBudget` for the blocks `M` that arise
here is not settled, and nothing below assumes it.

Nothing here discharges `NoDeepCollapse`, `NoDeepCollapseEmptyConj`,
`GreendlingerConclusion`, `GreendlingerTwoPiece`, `DeepCompositeLandsSharp` or
`DeepCompositeLandsSharp'`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  A long arc pins the relator length -/

/-- **More than half of a relator, inside a relator, has that relator's length.**

Rotate the occurrence to the front (`exists_prefix_mem_symmetrization_of_infix`):
either the rotation *is* `r`, and `|r| = |w|`, or `u` is a common prefix of two
distinct symmetrized relators, hence a piece, and `C'(lam)` caps it at
`lam·|r| < 2·lam·|u| ≤ |u|` -- against `|u| < lam·|r|`.

`GreendlingerEmptyConjCorner.not_short_arc_of_metric` is the reading of this that
supplies the contradiction from `|u| < lam·|w|`; this reading keeps the length
identity instead, which is what a *counting* argument needs.  Only `lam ≤ 1/2`
is used. -/
theorem length_eq_of_long_arc {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 2) (hmetric : MetricSmallCancellation R lam)
    {w r u : List (α × Bool)} (hw : w ∈ symmetrization R)
    (hr : r ∈ symmetrization R) (huw : u <:+: w) (hur : u <+: r)
    (hhalf : r.length < 2 * u.length) : r.length = w.length := by
  obtain ⟨v, hv, huv, hvlen⟩ := exists_prefix_mem_symmetrization_of_infix hw huw
  rcases eq_or_ne r v with h | h
  · rw [h, hvlen]
  · exfalso
    have hpiece : IsPiece (symmetrization R) u := ⟨r, hr, v, hv, h, hur, huv⟩
    have hfin : (u.length : ℚ) < lam * (r.length : ℚ) := hmetric u hpiece r hr hur
    have hcast : (r.length : ℚ) < 2 * (u.length : ℚ) := by exact_mod_cast hhalf
    have hrnn : (0 : ℚ) ≤ (r.length : ℚ) := by positivity
    rcases le_or_gt lam 0 with hl | hl
    · have h0 : lam * (r.length : ℚ) ≤ 0 * (r.length : ℚ) :=
        mul_le_mul_of_nonneg_right hl hrnn
      rw [zero_mul] at h0
      have hunn : (0 : ℚ) ≤ (u.length : ℚ) := by positivity
      linarith
    · have h1 : lam * (r.length : ℚ) < lam * (2 * (u.length : ℚ)) :=
        mul_lt_mul_of_pos_left hcast hl
      have h2 : 2 * lam * (u.length : ℚ) ≤ 1 * (u.length : ℚ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      rw [one_mul] at h2
      linarith

/-! ## 2.  The corner's counts -/

/-- **The survivor carries the ambient count.**  A collapsed configuration
computes `g = mk P'` (`mk_eq_of_collapse`), and the configuration itself is a
minimal expression for `g` of length `|e| + 1`.  So the word the corner hands
`GreendlingerConclusion` has minimal factor count exactly the count of the
configuration -- not one less.

This is the precise obstruction to an induction on factor count. -/
theorem emptyConj_survivor_count [DecidableEq α] {R : Set (List (α × Bool))}
    {t P' M B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk ([] : List (α × Bool)), t) :: e) g)
    (heq : palindrome ([] : List (α × Bool)) t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B') (hnil : B' = []) :
    IsMinimalConjProduct R (e.length + 1) (FreeGroup.mk P') := by
  have hg : g = FreeGroup.mk P' := mk_eq_of_collapse hmin heq htail hnil
  have h := isMinimalConjProduct_of_isMinimalConjExpr hmin
  rw [List.length_cons, hg] at h
  exact h

/-- **The survivor is the ambient word.**  Reduced words spelling the same
element are equal, so a collapsed configuration inside
`GreendlingerDeepInvariant.greendlingerAtSharp_drop_of_lands` -- whose ambient
word `w` satisfies `mk w = g` -- has `w = P'` on the nose.

Together with `emptyConj_survivor_count`, the Greendlinger input the corner
consumes is the conclusion for the *same word* at the *same count* as the step
producing it. -/
theorem emptyConj_word_eq [DecidableEq α] {R : Set (List (α × Bool))}
    {t P' M B' w : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk ([] : List (α × Bool)), t) :: e) g)
    (hredp : FreeGroup.IsReduced (palindrome ([] : List (α × Bool)) t))
    (heq : palindrome ([] : List (α × Bool)) t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B') (hnil : B' = [])
    (hw : FreeGroup.IsReduced w) (hgw : g = FreeGroup.mk w) : w = P' := by
  have hg : g = FreeGroup.mk P' := mk_eq_of_collapse hmin heq htail hnil
  have hsplit : t = P' ++ M := by
    have h := heq
    rwa [palindrome_nil] at h
  have hredt : FreeGroup.IsReduced t := by
    have h := hredp
    rwa [palindrome_nil] at h
  have hP'red : FreeGroup.IsReduced P' :=
    isReduced_of_infix ⟨[], M, by rw [List.nil_append]; exact hsplit.symm⟩ hredt
  have hmk : FreeGroup.mk w = FreeGroup.mk P' := by rw [← hgw, hg]
  have h6 := FreeGroup.reduce.sound hmk
  rwa [hw.reduce_eq, hP'red.reduce_eq] at h6

/-- **The block one factor down.**  `isMinimalConjExpr_tail_of_collapse` makes
the tail minimal for `(mk M)⁻¹`; reading it backwards (`isMinimalConjExpr_conjInv`)
makes `mk M` a minimal product of `|e|` conjugates.  That is the genuine drop the
collapse exposes -- one below the ambient `|e| + 1` of
`emptyConj_survivor_count`.

Also recorded: `M` is nonempty, reduced, and in the normal closure, so it is a
legitimate argument for any of the gate's conclusions. -/
theorem emptyConj_tail_block_data [DecidableEq α] {R : Set (List (α × Bool))}
    {t P' M B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk ([] : List (α × Bool)), t) :: e) g)
    (hredp : FreeGroup.IsReduced (palindrome ([] : List (α × Bool)) t))
    (heq : palindrome ([] : List (α × Bool)) t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : 0 < M.length) (hnil : B' = []) :
    M ≠ [] ∧ FreeGroup.IsReduced M ∧
      FreeGroup.mk M ∈ Subgroup.normalClosure (FreeGroup.mk '' R) ∧
      IsMinimalConjProduct R e.length (FreeGroup.mk M) := by
  have hsplit : t = P' ++ M := by
    have h := heq
    rwa [palindrome_nil] at h
  have hredt : FreeGroup.IsReduced t := by
    have h := hredp
    rwa [palindrome_nil] at h
  have hMne : M ≠ [] := by
    intro h
    rw [h, List.length_nil] at hlow
    omega
  have hredM : FreeGroup.IsReduced M :=
    isReduced_of_infix ⟨P', [], by rw [List.append_nil]; exact hsplit.symm⟩ hredt
  have h1 : IsMinimalConjExpr R e ((FreeGroup.mk M)⁻¹) :=
    isMinimalConjExpr_tail_of_collapse hmin htail hnil
  have h2 : IsMinimalConjExpr R (conjInv e) ((FreeGroup.mk M)⁻¹)⁻¹ :=
    isMinimalConjExpr_conjInv h1
  rw [inv_inv] at h2
  have h3 : IsMinimalConjProduct R (conjInv e).length (FreeGroup.mk M) :=
    isMinimalConjProduct_of_isMinimalConjExpr h2
  rw [length_conjInv] at h3
  exact ⟨hMne, hredM, mem_normalClosure_of_isConjProduct h3.1, h3⟩

/-! ## 3.  The half-form carries no information one factor down -/

/-- **The short prefix is shorter than the block.**  `|P'| < lam·|t|` with
`lam ≤ 1/2` and `t = P' ++ M` forces `2|P'| < |P'| + |M|`. -/
theorem length_lt_of_short_prefix {t P' M : List (α × Bool)} {lam : ℚ}
    (hlam : lam ≤ 1 / 2) (hsplit : t = P' ++ M)
    (hshort : (P'.length : ℚ) < lam * (t.length : ℚ)) : P'.length < M.length := by
  have hlen : t.length = P'.length + M.length := by
    rw [hsplit, List.length_append]
  have hlenQ : (t.length : ℚ) = (P'.length : ℚ) + (M.length : ℚ) := by
    exact_mod_cast hlen
  have hnn : (0 : ℚ) ≤ (t.length : ℚ) := by positivity
  have hb : lam * (t.length : ℚ) ≤ 1 / 2 * (t.length : ℚ) :=
    mul_le_mul_of_nonneg_right hlam hnn
  have hfin : (P'.length : ℚ) < (M.length : ℚ) := by linarith
  exact_mod_cast hfin

/-- **The half-form conclusion holds at the block, outright.**

`M` is a suffix of the symmetrized relator `t = P' ++ M` with `P'` shorter than
`M`, so the rotation `M ++ P'` is a symmetrized relator with `M` as a prefix and
`|M ++ P'| = |t| < 2|M|`.  The arc the gate asks for is `M` itself.

So the induction hypothesis available one factor down --- the half-form
conclusion at count `|e|` --- is *already true* of the block the collapse
exposes, and no contradiction can be extracted from it.  Together with
`emptyConj_survivor_count` and `emptyConj_word_eq` this is the whole verdict:
factor count does not descend at this leaf. -/
theorem greendlingerConclusion_holds_for_tail_block {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 2) {t P' M : List (α × Bool)}
    (ht : t ∈ symmetrization R) (hsplit : t = P' ++ M)
    (hshort : (P'.length : ℚ) < lam * (t.length : ℚ)) :
    ∃ r ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: M ∧ u <+: r ∧ r.length < 2 * u.length := by
  have hlt : P'.length < M.length := length_lt_of_short_prefix hlam hsplit hshort
  refine ⟨M ++ P', append_swap_mem_symmetrization (by rw [← hsplit]; exact ht), M,
    ⟨[], [], by rw [List.nil_append, List.append_nil]⟩, ⟨P', rfl⟩, ?_⟩
  rw [List.length_append]
  omega

/-! ## 4.  The lower-count input that would suffice -/

/-- **Two arcs on a budget.**  Two subwords of `w`, each more than half of a
symmetrized relator, whose lengths sum to at most `|w|`.

This is deliberately weaker than `GreendlingerInduction.TwoPieceConclusion`: the
arcs are not asked to be consecutive, ordered, or separated by anything -- only
to fit inside `w` together.  That is the entire content the refutation below
uses, and stating it separately keeps the refutation independent of the
ordering, which is exactly where `TwoPieceConclusion` is known to fail
(`GreendlingerTwoPieceRegime`). -/
def DisjointArcBudget (R : Set (List (α × Bool))) (w : List (α × Bool)) : Prop :=
  ∃ u₁ u₂ : List (α × Bool), u₁ <:+: w ∧ u₂ <:+: w ∧
    u₁.length + u₂.length ≤ w.length ∧
    (∃ r₁ ∈ symmetrization R, u₁ <+: r₁ ∧ r₁.length < 2 * u₁.length) ∧
    (∃ r₂ ∈ symmetrization R, u₂ <+: r₂ ∧ r₂.length < 2 * u₂.length)

/-- The two-piece conclusion supplies the budget: consecutive blocks of a
splitting of `w` fit inside `w`. -/
theorem disjointArcBudget_of_twoPieceConclusion {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (h : TwoPieceConclusion R w) : DisjointArcBudget R w := by
  obtain ⟨A, u₁, B, u₂, C, hw, h₁, h₂⟩ := h
  have hlen : w.length
      = A.length + u₁.length + B.length + u₂.length + C.length := by
    rw [hw, List.length_append, List.length_append, List.length_append,
      List.length_append]
  refine ⟨u₁, u₂, ⟨A, B ++ u₂ ++ C, ?_⟩, ⟨A ++ u₁ ++ B, C, hw.symm⟩, by omega,
    h₁, h₂⟩
  rw [hw]
  simp only [List.append_assoc]

/-- **A proper suffix of a symmetrized relator has no arc budget.**

`length_eq_of_long_arc` forces each arc's relator to have the length of `t`, so
each arc is longer than `|t|/2` and the two together are longer than `|t|`.  But
they fit inside `M`, and `|M| < |t|` because the discarded prefix `P'` is
nonempty.

Only `lam ≤ 1/2` is used, and none of the deep numerics: no `i`, no overrun
bound, no minimality. -/
theorem not_disjointArcBudget_of_relator_suffix {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 2) (hmetric : MetricSmallCancellation R lam)
    {t P' M : List (α × Bool)} (ht : t ∈ symmetrization R)
    (hsplit : t = P' ++ M) (hP'ne : P' ≠ [])
    (hbudget : DisjointArcBudget R M) : False := by
  obtain ⟨u₁, u₂, hu₁, hu₂, hfit, ⟨r₁, hr₁, hpre₁, hlt₁⟩, ⟨r₂, hr₂, hpre₂, hlt₂⟩⟩ :=
    hbudget
  have hMt : M <:+: t := ⟨P', [], by rw [List.append_nil]; exact hsplit.symm⟩
  have h₁ : r₁.length = t.length :=
    length_eq_of_long_arc hlam hmetric ht hr₁ (hu₁.trans hMt) hpre₁ hlt₁
  have h₂ : r₂.length = t.length :=
    length_eq_of_long_arc hlam hmetric ht hr₂ (hu₂.trans hMt) hpre₂ hlt₂
  have hlent : t.length = P'.length + M.length := by
    rw [hsplit, List.length_append]
  have hP'pos : 0 < P'.length := List.length_pos_iff.mpr hP'ne
  omega

/-- The budget hypothesis, graded by factor count: available for every word
whose minimal expression is *strictly shorter* than `n` factors. -/
def ArcBudgetBelow (R : Set (List (α × Bool))) (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → ∀ w : List (α × Bool), FreeGroup.IsReduced w → w ≠ [] →
    IsMinimalConjProduct R m (FreeGroup.mk w) → DisjointArcBudget R w

/-- **The corner at count `n`, from the budget at counts `< n`.**

The block `M` the collapse exposes has minimal factor count `|e|`, one below the
configuration's `|e| + 1` (`emptyConj_tail_block_data`), so `ArcBudgetBelow R n`
with `|e| < n` reaches it.  `not_disjointArcBudget_of_relator_suffix` then
refutes the collapse.

The consumption is strictly below the ambient count -- which is what the
half-form reduction of `GreendlingerEmptyConjCorner` is *not*, by
`emptyConj_survivor_count`.  The numeric hypotheses of the corner (`i`, the two
overrun bounds) go entirely unused, as does the adjacent factor.

This does not discharge anything: `DisjointArcBudget` is an open predicate, and
the statement stronger than it that the classical lemma is usually quoted as
(`GreendlingerInduction.GreendlingerTwoPiece`) is false. -/
theorem tail_ne_nil_of_arcBudgetBelow [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 2) (hmetric : MetricSmallCancellation R lam)
    {n : ℕ} (hbudget : ArcBudgetBelow R n)
    {t P' M B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hcount : e.length < n)
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk ([] : List (α × Bool)), t) :: e) g)
    (ht : t ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome ([] : List (α × Bool)) t))
    (heq : palindrome ([] : List (α × Bool)) t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : 0 < M.length) : B' ≠ [] := by
  intro hnil
  obtain ⟨hMne, hredM, -, hcnt⟩ :=
    emptyConj_tail_block_data hmin hredp heq htail hlow hnil
  have hP'ne : P' ≠ [] := prefix_ne_nil_of_collapse hmin heq htail hnil
  have hsplit : t = P' ++ M := by
    have h := heq
    rwa [palindrome_nil] at h
  exact not_disjointArcBudget_of_relator_suffix hlam hmetric ht hsplit hP'ne
    (hbudget e.length hcount M hredM hMne hcnt)

/-- The corner itself, from the ungraded budget.  Stated only to show the graded
form above is the whole of what is consumed; the hypothesis is open. -/
theorem noDeepCollapseEmptyConj_of_arcBudget [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 2)
    (hmetric : MetricSmallCancellation R lam)
    (hbudget : ∀ m : ℕ, ∀ w : List (α × Bool), FreeGroup.IsReduced w → w ≠ [] →
      IsMinimalConjProduct R m (FreeGroup.mk w) → DisjointArcBudget R w) :
    NoDeepCollapseEmptyConj R lam := by
  intro c t _c₂ _t₂ e _f g P' M B' _i hc hmin _hmin₂ ht _ht₂ hredp _hredp₂ heq
    htail hlow _hi _hgt
  subst hc
  rw [List.length_nil] at hlow
  exact tail_ne_nil_of_arcBudgetBelow (n := e.length + 1) hlam hmetric
    (fun m _ w hw hwne hm => hbudget m w hw hwne hm) (by omega) hmin ht hredp heq
    htail hlow

end SmallCancellationRouter
end GroupApproximation
