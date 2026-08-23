import GroupApproximation.Sofic.GreendlingerCollapseInduction

/-!
# The two-arc demand, located cyclically

`GreendlingerCollapseInduction` shows that the last deep gap
`NoDeepCollapseEmptyConj` does not descend on factor count through the half-form
`GreendlingerConclusion`, and isolates the one hypothesis that *is* consumed one
factor below the ambient count: `DisjointArcBudget`, two arcs of the word each
more than half of a symmetrized relator, whose lengths sum to at most the word's
length.  It also flags the danger: `DisjointArcBudget` is implied by
`GreendlingerInduction.TwoPieceConclusion`, and `TwoPieceConclusion` is *false* —
`GreendlingerTwoPieceRegime` carries the counterexample.

This file settles whether the counterexample also kills `DisjointArcBudget`, and
formulates the cyclic statement that replaces `TwoPieceConclusion`.

## 1.  The counterexample does **not** kill `DisjointArcBudget`

`DisjointArcBudget` never asked its two arcs to sit at *different* positions —
only that their lengths fit inside the word.  So a single arc, taken twice,
supplies it whenever the arc is at most half the word:

    `DisjointArcBudget R w  ↔  ∃ u <:+: w, 2·|u| ≤ |w| and u is more than half
    of a symmetrized relator`

(`disjointArcBudget_iff`; the forward direction is `min` over an unordered pair,
`exists_double_of_disjointArcBudget`).  In the counterexample word

```text
    w  =  q(45)  ++  t.take 90  ++  t'.drop 55(45)          |w| = 180
```

every arc that is more than half of a relator lies inside the 90-letter block —
that is exactly what makes `TwoPieceConclusion` fail there, since two *disjoint*
such arcs would need `51 + 51 = 102` letters inside a block of `90`.  But
`t.take 90` is itself such an arc, `|t| = 100 < 180 = 2·90`, and
`2·90 = 180 ≤ 180 = |w|`.  So the budget holds, on the nose and with no slack to
spare: `disjointArcBudget_counterexample`.

**Verdict: `DisjointArcBudget` survives the counterexample.**  The two-arc route
of `GreendlingerCollapseInduction` is not closed by it.

The equivalence also says what the route really needs, which is *not* a two-arc
statement: one arc, at most half the word.  What the counterexample refutes is
the *positional* reading — two arcs at disjoint positions, ordered along `w` —
and `not_disjointArcBudget_of_relator_suffix` never used the positions.

## 2.  The cyclic statement

`GreendlingerTwoPieceRegime`'s header records what the second region of the
counterexample does satisfy: `t'.drop 55 ++ q` is 90 letters of a *rotation* of
`t'`, consecutive along `∂D₂` and not along `w`.  `TwoPieceCyclic` is that
statement: some rotation of `w` splits as `A ++ u₁ ++ B ++ u₂ ++ C` with `u₁`,
`u₂` each more than half of a symmetrized relator.  It holds in the
counterexample (`twoPieceCyclic_counterexample`), it is implied by the linear
form (`twoPieceCyclic_of_twoPieceConclusion`), and it says what happens at the
basepoint: the basepoint is a cut of `w = X ++ Y` and the rotation is `Y ++ X`,
so it falls inside exactly one of the five blocks.

`CyclicInfix` is the resulting notion of occurrence — inside `w`, or straddling
the basepoint as a suffix of `w` followed by a prefix of `w` — and
`cyclicArcBudget_of_twoPieceCyclic` extracts from `TwoPieceCyclic` the fact that
**at most one of the two arcs straddles**: one is a genuine infix of `w`, the
other is a `CyclicInfix`, and their lengths still sum to at most `|w|`.  That is
`CyclicArcBudget`.

## 3.  The cyclic budget refutes the corner's blocks outright

`not_cyclicArcBudget_of_relator_suffix` is the payoff.  For a proper suffix `M`
of a symmetrized relator `t`:

* the non-straddling arc `u₁` is an infix of `t`, so `length_eq_of_long_arc`
  forces `|r₁| = |t|`, hence `|t| < 2|u₁|`;
* the budget then leaves `2|u₂| < |t|`, so `|r₂| < |t|`;
* if `u₂` does not straddle it is an infix of `t` too and `|r₂| = |t|` — against
  the line above;
* if `u₂ = A ++ B` straddles, then `A` is a prefix of `r₂` and an infix of `t`,
  and `B` is an infix of both `r₂` and `t`; `|r₂| < |t|` makes each of them a
  *piece*, so `C'(lam)` gives `|A| + |B| < 2·lam·|r₂| < 4·lam·|u₂| ≤ |u₂|` at
  `lam ≤ 1/4`.

So the straddling case is killed by the piece bound rather than by counting, and
the cyclic budget is contradictory at these blocks — strictly more than
`not_disjointArcBudget_of_relator_suffix` needs
(`disjointArcBudget_of_cyclicArcBudget_of_relator_suffix` records that the
implication asked for is vacuous, not informative).

`tail_ne_nil_of_cyclicArcBudgetBelow` then closes the corner at count `n` from
`CyclicArcBudgetBelow R n`, consumption strictly below the ambient count, exactly
as in `GreendlingerCollapseInduction`.

**`CyclicArcBudget` is an open predicate and nothing below assumes it.**  Nothing
here discharges `NoDeepCollapse`, `NoDeepCollapseEmptyConj`,
`GreendlingerConclusion`, `GreendlingerTwoPiece`, `TwoPieceCyclic`,
`DeepCompositeLandsSharp` or `DeepCompositeLandsSharp'`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  A long arc, and the arc budget as a one-arc statement -/

/-- **More than half of a symmetrized relator.**  The property both arcs of
`DisjointArcBudget` are asked to have, named so the cyclic statements below can
quote it. -/
def LongArc (R : Set (List (α × Bool))) (u : List (α × Bool)) : Prop :=
  ∃ r ∈ symmetrization R, u <+: r ∧ r.length < 2 * u.length

/-- A long arc is nonempty: an empty arc would make its relator shorter than
`0`. -/
theorem length_pos_of_longArc {R : Set (List (α × Bool))} {u : List (α × Bool)}
    (h : LongArc R u) : 0 < u.length := by
  obtain ⟨r, -, -, hlt⟩ := h
  omega

/-- **The budget from a single arc, doubled.**  `DisjointArcBudget` asks its two
arcs to fit inside the word together; it does not ask them to sit at different
positions, so one arc of at most half the word supplies both. -/
theorem disjointArcBudget_of_double {R : Set (List (α × Bool))}
    {w u : List (α × Bool)} (hu : u <:+: w) (hfit : 2 * u.length ≤ w.length)
    (hlong : LongArc R u) : DisjointArcBudget R w :=
  ⟨u, u, hu, hu, by omega, hlong, hlong⟩

/-- **The budget gives back a single arc, doubled.**  The shorter of the two
arcs fits twice, because both are drawn from the same set. -/
theorem exists_double_of_disjointArcBudget {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (h : DisjointArcBudget R w) :
    ∃ u : List (α × Bool), u <:+: w ∧ 2 * u.length ≤ w.length ∧ LongArc R u := by
  obtain ⟨u₁, u₂, h₁, h₂, hfit, hlong₁, hlong₂⟩ := h
  rcases le_or_gt u₁.length u₂.length with hle | hlt
  · exact ⟨u₁, h₁, by omega, hlong₁⟩
  · exact ⟨u₂, h₂, by omega, hlong₂⟩

/-- **The arc budget is a one-arc statement.**  Two arcs on a budget is exactly
one arc of at most half the word.

This is the precise content of the predicate `GreendlingerCollapseInduction`
isolates, and it is what makes the two-arc route immune to the counterexample of
`GreendlingerTwoPieceRegime`: that counterexample refutes two arcs at *disjoint
positions*, and positions never entered here. -/
theorem disjointArcBudget_iff {R : Set (List (α × Bool))}
    {w : List (α × Bool)} :
    DisjointArcBudget R w ↔
      ∃ u : List (α × Bool), u <:+: w ∧ 2 * u.length ≤ w.length ∧ LongArc R u :=
  ⟨exists_double_of_disjointArcBudget,
   fun ⟨_u, hu, hfit, hlong⟩ => disjointArcBudget_of_double hu hfit hlong⟩

/-- **A long arc with room on both sides supplies the budget.**  The shape of
the counterexample word: a long block with the rest of the word split around
it. -/
theorem disjointArcBudget_of_long_arc_block {R : Set (List (α × Bool))}
    {X u Y : List (α × Bool)} (hlong : LongArc R u)
    (hfit : u.length ≤ X.length + Y.length) :
    DisjointArcBudget R (X ++ u ++ Y) := by
  have hlen : (X ++ u ++ Y).length = X.length + u.length + Y.length := by
    rw [List.length_append, List.length_append]
  exact disjointArcBudget_of_double ⟨X, Y, rfl⟩ (by omega) hlong

/-- **The counterexample word has an arc budget.**

The word of `GreendlingerTwoPieceRegime`'s header, with its lengths written out:
`|t| = |t'| = 100`, `|E| = 10`, and

```text
    w  =  q(45)  ++  t.take 90  ++  t'.drop 55(45)          |w| = 180
```

`TwoPieceConclusion` fails there because two arcs at *disjoint positions* would
need `102` letters inside the 90-letter block.  `DisjointArcBudget` does not:
`t.take 90` is more than half of `t` (`100 < 180`) and fits twice inside `w`
(`180 ≤ 180`).

So the counterexample does **not** refute `DisjointArcBudget`, and the route of
`GreendlingerCollapseInduction.tail_ne_nil_of_arcBudgetBelow` is not closed by
it. -/
theorem disjointArcBudget_counterexample {R : Set (List (α × Bool))}
    {t q u B' : List (α × Bool)} (ht : t ∈ symmetrization R) (hu : u <+: t)
    (htlen : t.length = 100) (hulen : u.length = 90)
    (hqlen : q.length = 45) (hBlen : B'.length = 45) :
    DisjointArcBudget R (q ++ u ++ B') :=
  disjointArcBudget_of_long_arc_block ⟨t, ht, hu, by omega⟩ (by omega)

/-! ## 2.  Occurrence in the cyclic word -/

/-- **Occurrence in the cyclic word `w`, with the basepoint named.**  A subword
of the cyclic word either sits inside `w`, or straddles the basepoint: a suffix
of `w` followed by a prefix of `w`.

This is the notion `GreendlingerTwoPieceRegime`'s header asks for.  The second
region of the counterexample there realizes the second disjunct: `t'.drop 55` is
a suffix of `w` and `q` is a prefix of `w`, and `t'.drop 55 ++ q` is 90 letters
of a rotation of `t'` -- consecutive along `∂D₂`, not along `w`. -/
def CyclicInfix (u w : List (α × Bool)) : Prop :=
  u <:+: w ∨ ∃ A B : List (α × Bool), u = A ++ B ∧ A <:+ w ∧ B <+: w

/-- An ordinary occurrence is a cyclic occurrence. -/
theorem cyclicInfix_of_infix {u w : List (α × Bool)} (h : u <:+: w) :
    CyclicInfix u w :=
  Or.inl h

/-- **Reading an occurrence across the basepoint.**  If `u` occurs inside
`A ++ B`, where `A` is a suffix and `B` a prefix of `w`, then `u` occurs
cyclically in `w`.

Three positions, and `List.append_eq_append_iff` separates them: `u` inside `B`,
`u` inside `A`, or `u` across the seam -- and only the third is a straddle. -/
theorem cyclicInfix_of_infix_append {w A B u : List (α × Bool)}
    (hA : A <:+ w) (hB : B <+: w) (hu : u <:+: A ++ B) : CyclicInfix u w := by
  obtain ⟨p, s, hps⟩ := hu
  have h : A ++ B = p ++ (u ++ s) := by
    rw [← hps, List.append_assoc]
  rcases List.append_eq_append_iff.mp h with ⟨a', -, hB'⟩ | ⟨c', hA', hd⟩
  · have hinB : u <:+: B := ⟨a', s, by rw [List.append_assoc]; exact hB'.symm⟩
    exact cyclicInfix_of_infix (hinB.trans hB.isInfix)
  · have hc'A : c' <:+ A := ⟨p, hA'.symm⟩
    rcases List.append_eq_append_iff.mp hd with ⟨a'', hc', -⟩ | ⟨c'', hu', hB''⟩
    · have huc' : u <+: c' := ⟨a'', hc'.symm⟩
      exact cyclicInfix_of_infix
        ((huc'.isInfix.trans hc'A.isInfix).trans hA.isInfix)
    · have hc''B : c'' <+: B := ⟨s, hB''.symm⟩
      exact Or.inr ⟨c', c'', hu', hc'A.trans hA, hc''B.trans hB⟩

/-! ## 3.  The cyclic two-arc statement -/

/-- **Two long arcs, located cyclically.**  Some rotation of `w` splits into
five consecutive blocks with the second and fourth each more than half of a
symmetrized relator.

The basepoint is explicit: `w = X ++ Y` is the cut, `Y ++ X` is the rotation,
and the seam therefore falls inside exactly one of `A`, `u₁`, `B`, `u₂`, `C`.
This is the statement Greendlinger's lemma proves for a reduced diagram with at
least two regions -- the arcs lie on `∂D`, which is the *cyclic* word -- and it
is what `GreendlingerInduction.TwoPieceConclusion` asks for with the rotation
suppressed.  Suppressing it is exactly the step that makes `TwoPieceConclusion`
false: see `twoPieceCyclic_counterexample`. -/
def TwoPieceCyclic (R : Set (List (α × Bool))) (w : List (α × Bool)) : Prop :=
  ∃ X Y A u₁ B u₂ C : List (α × Bool),
    w = X ++ Y ∧ Y ++ X = A ++ u₁ ++ B ++ u₂ ++ C ∧ LongArc R u₁ ∧ LongArc R u₂

/-- **The cyclic arc budget.**  Two long arcs fitting inside `w` together, one
of them an honest infix and the other allowed to straddle the basepoint.

This is `DisjointArcBudget` with exactly one concession, and
`cyclicArcBudget_of_disjointArcBudget` shows it is the weaker hypothesis --- so
it is the easier one to supply, while `not_cyclicArcBudget_of_relator_suffix`
shows it is still strong enough to refute the corner's blocks. -/
def CyclicArcBudget (R : Set (List (α × Bool))) (w : List (α × Bool)) : Prop :=
  ∃ u₁ u₂ : List (α × Bool), u₁ <:+: w ∧ CyclicInfix u₂ w ∧
    u₁.length + u₂.length ≤ w.length ∧ LongArc R u₁ ∧ LongArc R u₂

/-- The linear budget is a cyclic budget: no arc straddles. -/
theorem cyclicArcBudget_of_disjointArcBudget {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (h : DisjointArcBudget R w) : CyclicArcBudget R w := by
  obtain ⟨u₁, u₂, h₁, h₂, hfit, hl₁, hl₂⟩ := h
  exact ⟨u₁, u₂, h₁, cyclicInfix_of_infix h₂, hfit, hl₁, hl₂⟩

/-- The linear two-piece conclusion is a cyclic one: take the trivial
rotation. -/
theorem twoPieceCyclic_of_twoPieceConclusion {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (h : TwoPieceConclusion R w) : TwoPieceCyclic R w := by
  obtain ⟨A, u₁, B, u₂, C, hw, ⟨r₁, hr₁, hpre₁, hlt₁⟩, ⟨r₂, hr₂, hpre₂, hlt₂⟩⟩ := h
  refine ⟨w, [], A, u₁, B, u₂, C, (List.append_nil w).symm, ?_,
    ⟨r₁, hr₁, hpre₁, hlt₁⟩, ⟨r₂, hr₂, hpre₂, hlt₂⟩⟩
  rw [List.nil_append]
  exact hw

/-- **At most one of the two arcs straddles the basepoint.**

The five blocks are disjoint along the rotation, so the seam lies inside at most
one of `u₁`, `u₂`; `List.append_eq_append_iff` locates it on one side or the
other of the pair, and the arc on the far side is an honest infix of `w`.  The
lengths still sum to at most `|w|`, because the rotation has the same length. -/
theorem cyclicArcBudget_of_twoPieceCyclic {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (h : TwoPieceCyclic R w) : CyclicArcBudget R w := by
  obtain ⟨X, Y, A, u₁, B, u₂, C, hw, hrot, hlong₁, hlong₂⟩ := h
  have hXpre : X <+: w := ⟨Y, hw.symm⟩
  have hYsuf : Y <:+ w := ⟨X, hw.symm⟩
  have hlenw : w.length = X.length + Y.length := by
    rw [hw, List.length_append]
  have hlenYX : (Y ++ X).length = Y.length + X.length := by
    rw [List.length_append]
  have hlenrot : (Y ++ X).length
      = A.length + u₁.length + B.length + u₂.length + C.length := by
    rw [hrot, List.length_append, List.length_append, List.length_append,
      List.length_append]
  have hgroup : Y ++ X = (A ++ u₁ ++ B) ++ (u₂ ++ C) := by
    rw [hrot]
    simp only [List.append_assoc]
  rcases List.append_eq_append_iff.mp hgroup with ⟨z, hz₁, hz₂⟩ | ⟨z, hz₁, hz₂⟩
  · -- the seam falls at or before `u₂`: `u₂` lies inside the prefix `X`
    have hu₂X : u₂ <:+: X := ⟨z, C, by rw [List.append_assoc]; exact hz₂.symm⟩
    have hzX : z <+: X := ⟨u₂ ++ C, hz₂.symm⟩
    have hzw : z <+: w := hzX.trans hXpre
    exact ⟨u₂, u₁, hu₂X.trans hXpre.isInfix,
      cyclicInfix_of_infix_append hYsuf hzw ⟨A, B, hz₁⟩, by omega, hlong₂, hlong₁⟩
  · -- the seam falls at or after `u₂`: `u₁` lies inside the suffix `Y`
    have hABY : A ++ u₁ ++ B <+: Y := ⟨z, hz₁.symm⟩
    have hzY : z <:+ Y := ⟨A ++ u₁ ++ B, hz₁.symm⟩
    have hzw : z <:+ w := hzY.trans hYsuf
    have hu₁ABB : u₁ <:+: A ++ u₁ ++ B := ⟨A, B, rfl⟩
    have hu₂zX : u₂ <+: z ++ X := ⟨C, hz₂⟩
    exact ⟨u₁, u₂,
      ((hu₁ABB.trans hABY.isInfix).trans hYsuf.isInfix),
      cyclicInfix_of_infix_append hzw hXpre hu₂zX.isInfix,
      by omega, hlong₁, hlong₂⟩

/-- **The counterexample's shape, cyclically.**  A word `q ++ (u ++ B')` whose
middle block is a long arc and whose *outer* blocks, read in the other cyclic
order, prefix a symmetrized relator that they are more than half of.

Nothing here is disjoint along `q ++ (u ++ B')`: the second arc `B' ++ q` is a
suffix followed by a prefix. -/
theorem twoPieceCyclic_of_split {R : Set (List (α × Bool))}
    {q u B' s : List (α × Bool)} (hu : LongArc R u)
    (hr : B' ++ (q ++ s) ∈ symmetrization R)
    (hlt : (B' ++ (q ++ s)).length < 2 * (B' ++ q).length) :
    TwoPieceCyclic R (q ++ (u ++ B')) := by
  refine ⟨q, u ++ B', [], u, [], B' ++ q, [], rfl, ?_, hu,
    ⟨B' ++ (q ++ s), hr, ⟨s, List.append_assoc B' q s⟩, hlt⟩⟩
  simp only [List.nil_append, List.append_nil, List.append_assoc]

/-- **The counterexample satisfies the cyclic statement.**

`GreendlingerTwoPieceRegime`'s header, with the lengths written out: `|t| = 100`,
`u = t.take 90`, `q = t'.take 45`, `B' = t'.drop 55`, and `s` the ten letters
`(t'.take 55).drop 45`, so that `B' ++ (q ++ s)` is the rotation
`t'.drop 55 ++ t'.take 55` of `t'`.  Then

```text
    w  =  q(45)  ++  t.take 90  ++  t'.drop 55(45)          |w| = 180
```

and the rotation `(u ++ B') ++ q` splits as `u(90) ++ (B' ++ q)(90)`, with
`|t| = 100 < 180` and `|t'| = 100 < 180`.

`TwoPieceConclusion R w` is false -- two arcs at disjoint positions *along `w`*
would need 102 letters inside the 90-letter block.  `TwoPieceCyclic R w` holds.
That is the whole difference between the two statements. -/
theorem twoPieceCyclic_counterexample {R : Set (List (α × Bool))}
    {t q u B' s : List (α × Bool)} (ht : t ∈ symmetrization R) (hut : u <+: t)
    (hrot : B' ++ (q ++ s) ∈ symmetrization R)
    (htlen : t.length = 100) (hulen : u.length = 90)
    (hqlen : q.length = 45) (hBlen : B'.length = 45) (hslen : s.length = 10) :
    TwoPieceCyclic R (q ++ (u ++ B')) :=
  twoPieceCyclic_of_split ⟨t, ht, hut, by omega⟩ hrot
    (by simp only [List.length_append]; omega)

/-! ## 4.  The cyclic budget is refuted at a relator suffix -/

/-- **A proper suffix of a symmetrized relator has no cyclic arc budget.**

The non-straddling arc `u₁` is an infix of `t`, so `length_eq_of_long_arc` pins
`|r₁| = |t|` and `|t| < 2|u₁|`.  The budget then leaves `2|u₂| < |t|`, hence
`|r₂| < |t|`, and the second arc has nowhere to go:

* if it does not straddle it is an infix of `t` too, and `length_eq_of_long_arc`
  makes `|r₂| = |t|`;
* if it straddles, `u₂ = A ++ B` with `A <:+ M` and `B <+: M`.  Both are infixes
  of `t`, and `|r₂| < |t|` makes the rotation of `t` carrying each of them a
  *different* symmetrized relator from the one `r₂` supplies -- so each is a
  piece, and `C'(lam)` gives `|A| + |B| < 2·lam·|r₂| < 4·lam·|u₂| ≤ |u₂|`.

The straddling case is closed by the piece bound, not by counting, and that is
the whole reason the cyclic weakening costs nothing here.  `lam ≤ 1/4` is what
is used: `1/2` for `length_eq_of_long_arc`, `1/4` for the display above.  No
`i`, no overrun bound, no minimality. -/
theorem not_cyclicArcBudget_of_relator_suffix {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1 / 4) (hmetric : MetricSmallCancellation R lam)
    {t P' M : List (α × Bool)} (ht : t ∈ symmetrization R)
    (hsplit : t = P' ++ M) (hP'ne : P' ≠ [])
    (hbudget : CyclicArcBudget R M) : False := by
  obtain ⟨u₁, u₂, hu₁, hu₂, hfit, ⟨r₁, hr₁, hpre₁, hlt₁⟩, ⟨r₂, hr₂, hpre₂, hlt₂⟩⟩ :=
    hbudget
  have hMt : M <:+: t := ⟨P', [], by rw [List.append_nil]; exact hsplit.symm⟩
  have hhalf : lam ≤ 1 / 2 := by linarith
  have h₁ : r₁.length = t.length :=
    length_eq_of_long_arc hhalf hmetric ht hr₁ (hu₁.trans hMt) hpre₁ hlt₁
  have hlent : t.length = P'.length + M.length := by
    rw [hsplit, List.length_append]
  have hP'pos : 0 < P'.length := List.length_pos_iff.mpr hP'ne
  have hu₂lt : 2 * u₂.length < t.length := by omega
  rcases hu₂ with hin | ⟨A, B, hAB, hA, hB⟩
  · have h₂ : r₂.length = t.length :=
      length_eq_of_long_arc hhalf hmetric ht hr₂ (hin.trans hMt) hpre₂ hlt₂
    omega
  · subst hAB
    have hr₂lt : r₂.length < t.length := by omega
    -- the head of the straddling arc is a piece
    have hAAB : A <+: A ++ B := ⟨B, rfl⟩
    have hApre : A <+: r₂ := hAAB.trans hpre₂
    obtain ⟨v, hv, hAv, hvlen⟩ :=
      exists_prefix_mem_symmetrization_of_infix ht (hA.isInfix.trans hMt)
    have hnev : r₂ ≠ v := by
      intro hEq
      rw [hEq] at hr₂lt
      omega
    have hboundA : (A.length : ℚ) < lam * (r₂.length : ℚ) :=
      hmetric A ⟨r₂, hr₂, v, hv, hnev, hApre, hAv⟩ r₂ hr₂ hApre
    -- and so is its tail
    have hBAB : B <:+ A ++ B := ⟨A, rfl⟩
    have hBinf : B <:+: r₂ := hBAB.isInfix.trans hpre₂.isInfix
    obtain ⟨r₃, hr₃, hBr₃, hr₃len⟩ :=
      exists_prefix_mem_symmetrization_of_infix hr₂ hBinf
    obtain ⟨v', hv', hBv', hv'len⟩ :=
      exists_prefix_mem_symmetrization_of_infix ht (hB.isInfix.trans hMt)
    have hnev' : r₃ ≠ v' := by
      intro hEq
      rw [hEq, hv'len] at hr₃len
      omega
    have hboundB₀ : (B.length : ℚ) < lam * (r₃.length : ℚ) :=
      hmetric B ⟨r₃, hr₃, v', hv', hnev', hBr₃, hBv'⟩ r₃ hr₃ hBr₃
    have hboundB : (B.length : ℚ) < lam * (r₂.length : ℚ) := by
      rwa [hr₃len] at hboundB₀
    -- the two piece bounds do not leave room for more than half a relator
    have hsum : ((A ++ B).length : ℚ) = (A.length : ℚ) + (B.length : ℚ) := by
      have hn : (A ++ B).length = A.length + B.length := by
        rw [List.length_append]
      exact_mod_cast hn
    have hcast : (r₂.length : ℚ) < 2 * ((A ++ B).length : ℚ) := by
      exact_mod_cast hlt₂
    have hLnn : (0 : ℚ) ≤ ((A ++ B).length : ℚ) := by positivity
    have hRnn : (0 : ℚ) ≤ (r₂.length : ℚ) := by positivity
    rcases le_or_gt lam 0 with hl | hl
    · have h0 : lam * (r₂.length : ℚ) ≤ 0 * (r₂.length : ℚ) :=
        mul_le_mul_of_nonneg_right hl hRnn
      rw [zero_mul] at h0
      linarith
    · have h1 : lam * (r₂.length : ℚ) < lam * (2 * ((A ++ B).length : ℚ)) :=
        mul_lt_mul_of_pos_left hcast hl
      have h1' : lam * (2 * ((A ++ B).length : ℚ))
          = 2 * lam * ((A ++ B).length : ℚ) := by ring
      rw [h1'] at h1
      have h2 : 4 * lam * ((A ++ B).length : ℚ) ≤ 1 * ((A ++ B).length : ℚ) :=
        mul_le_mul_of_nonneg_right (by linarith) hLnn
      rw [one_mul] at h2
      linarith

/-- **The implication asked for is vacuous.**  `GreendlingerCollapseInduction`
asks whether the cyclic statement supplies `DisjointArcBudget` for the blocks
`M` that arise in the collapse corner.  It does, but only because the cyclic
budget is already contradictory there: the straddling arc is refuted directly,
so nothing has to be transported back to a linear occurrence.

Recorded so the shape of the answer is not mistaken for content -- the useful
statement is `not_cyclicArcBudget_of_relator_suffix`, not this. -/
theorem disjointArcBudget_of_cyclicArcBudget_of_relator_suffix
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 4)
    (hmetric : MetricSmallCancellation R lam)
    {t P' M : List (α × Bool)} (ht : t ∈ symmetrization R)
    (hsplit : t = P' ++ M) (hP'ne : P' ≠ [])
    (hbudget : CyclicArcBudget R M) : DisjointArcBudget R M :=
  absurd hbudget (fun h =>
    not_cyclicArcBudget_of_relator_suffix hlam hmetric ht hsplit hP'ne h)

/-! ## 5.  The corner, from the cyclic budget one factor down -/

/-- The cyclic budget hypothesis, graded by factor count: available for every
word whose minimal expression is *strictly shorter* than `n` factors. -/
def CyclicArcBudgetBelow (R : Set (List (α × Bool))) (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → ∀ w : List (α × Bool), FreeGroup.IsReduced w → w ≠ [] →
    IsMinimalConjProduct R m (FreeGroup.mk w) → CyclicArcBudget R w

/-- The linear grading implies the cyclic one, so this is the weaker gate. -/
theorem cyclicArcBudgetBelow_of_arcBudgetBelow {R : Set (List (α × Bool))}
    {n : ℕ} (h : ArcBudgetBelow R n) : CyclicArcBudgetBelow R n :=
  fun m hm w hw hwne hmin =>
    cyclicArcBudget_of_disjointArcBudget (h m hm w hw hwne hmin)

/-- **The corner at count `n`, from the cyclic budget at counts `< n`.**

Identical plumbing to
`GreendlingerCollapseInduction.tail_ne_nil_of_arcBudgetBelow`: the block `M` the
collapse exposes has minimal factor count `|e|`, one below the configuration's
`|e| + 1` (`emptyConj_tail_block_data`), so the graded hypothesis reaches it and
`not_cyclicArcBudget_of_relator_suffix` refutes the collapse.  The consumption
is strictly below the ambient count, which is what the half-form reduction of
`GreendlingerEmptyConjCorner` is not.

The hypothesis is weaker than `ArcBudgetBelow`
(`cyclicArcBudgetBelow_of_arcBudgetBelow`) and it is the one Greendlinger's
lemma is actually about, because the arcs it locates lie on the boundary cycle.
It is still an open predicate. -/
theorem tail_ne_nil_of_cyclicArcBudgetBelow [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 4)
    (hmetric : MetricSmallCancellation R lam)
    {n : ℕ} (hbudget : CyclicArcBudgetBelow R n)
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
  exact not_cyclicArcBudget_of_relator_suffix hlam hmetric ht hsplit hP'ne
    (hbudget e.length hcount M hredM hMne hcnt)

/-- The corner itself, from the ungraded cyclic budget.  Stated only to show the
graded form above is the whole of what is consumed; the hypothesis is open. -/
theorem noDeepCollapseEmptyConj_of_cyclicArcBudget [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 4)
    (hmetric : MetricSmallCancellation R lam)
    (hbudget : ∀ m : ℕ, ∀ w : List (α × Bool), FreeGroup.IsReduced w → w ≠ [] →
      IsMinimalConjProduct R m (FreeGroup.mk w) → CyclicArcBudget R w) :
    NoDeepCollapseEmptyConj R lam := by
  intro c t _c₂ _t₂ e _f g P' M B' _i hc hmin _hmin₂ ht _ht₂ hredp _hredp₂ heq
    htail hlow _hi _hgt
  subst hc
  rw [List.length_nil] at hlow
  exact tail_ne_nil_of_cyclicArcBudgetBelow (n := e.length + 1) hlam hmetric
    (fun m _ w hw hwne hm => hbudget m w hw hwne hm) (by omega) hmin ht hredp heq
    htail hlow

/-- The residual, from the same input. -/
theorem noDeepCollapse_of_cyclicArcBudget [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 4)
    (hmetric : MetricSmallCancellation R lam)
    (hbudget : ∀ m : ℕ, ∀ w : List (α × Bool), FreeGroup.IsReduced w → w ≠ [] →
      IsMinimalConjProduct R m (FreeGroup.mk w) → CyclicArcBudget R w) :
    NoDeepCollapse R lam :=
  noDeepCollapse_of_emptyConj
    (noDeepCollapseEmptyConj_of_cyclicArcBudget hlam hmetric hbudget)

end SmallCancellationRouter
end GroupApproximation
