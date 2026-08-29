import GroupApproximation.Sofic.MatchingFoldObstruction
import GroupApproximation.Sofic.MatchingFactorPair

/-!
# The folded order, and planarity read in it

`MatchingFoldObstruction` shows the naive fold is not non-crossing **in the
original linear order**, and its header names the two ways out: exclude the
configuration by some hypothesis not yet spent, or "carry the boundary-walk
reordering that folding actually induces".  Two model tests have now closed the
first way out -- `Osin24FoldWitnessLegality` shows the metric condition does not
exclude it, and the second instance below shows the configuration survives even
when the cancelling region is partial at both ends.  This module takes the
second way out and states what has to be true.

## The two instances, which are what the statement must survive

Both are legal `C'(1/6)` families: every relator is one letter or has pairwise
distinct letters, so the only piece is empty.

**Instance I** (`Osin24FoldWitnessLegality`).  `R = {[u],[q],[z]}`,
`e = [([],[u]), ([],[q⁻¹]), ([],[u⁻¹]), ([u],[q]), ([],[z])]`, `w = [z]`.
Labelled word, eight letters:

    0:u(rel C) 1:q⁻¹(rel A) 2:u⁻¹(rel B) 3:u(conj D) 4:q(rel D) 5:u⁻¹(stem D)
    6:z(rel E) 7:z⁻¹(boundary)

matching `(2,3), (1,4), (0,5), (6,7)`; `D`'s mirror is `(3,5)`.  The transfer is
`(0,2), (1,4), (6,7)`, and `0 < 1 < 2 < 4` straddles.

**Instance II** (this module's contribution, and the one the straddle hunt
produced).  `R = {[x,u],[q],[z]}`,
`e = [([],[x,u]), ([],[q⁻¹]), ([],[u⁻¹,x⁻¹]), ([x,u],[q]), ([],[z])]`,
`w = [z]`.  Labelled word, twelve letters:

    0:x 1:u (rel C) | 2:q⁻¹ (rel A) | 3:u⁻¹ 4:x⁻¹ (rel B)
    | 5:x 6:u (conj D) 7:q (rel D) 8:u⁻¹ 9:x⁻¹ (stem D) | 10:z (rel E)
    | 11:z⁻¹ (boundary)

matching `(4,5), (3,6), (2,7), (1,8), (0,9), (10,11)`; `D`'s mirrors are `(5,9)`
and `(6,8)`.  The transfer is `(0,4), (1,3), (2,7), (10,11)`, and
`1 < 2 < 3 < 7` straddles.

Instance II is the sharper one: its cancelling region `[1,8]` begins strictly
inside a relator block (position `0` is the same block) and ends strictly inside
a stem block (position `9` is the same block), so it is not a union of whole
factors.  It is still excluded by minimality, but through the pair `(A, D)` --
`A`'s relator is one letter and that letter is entirely consumed -- which a
longer relator would remove.  Neither instance is excluded by the metric
condition, and the pairwise lemma is order-blind, so neither can be what makes
the fold work.

## What the folded order is

Folding a conjugator edge identifies the two sides of it, and the blocks glued
to those two sides become adjacent.  In both instances the effect is the same
and is visible in the transfer: `D`'s conjugator is glued to `B` on one side and
to `C` on the other, so after folding `C` and `B` are joined, and the order that
sees it is `C, B, A, D, E, boundary` -- `B` moves in front of `A`.  In the
original order `C < A < B`, which is exactly why the chord `C–B` straddles the
chord `A–D`.

`ordOne` and `ordTwo` below are that order, written out, and the four theorems
of section 4 are the model test: in the identity order the transfer straddles,
in the folded order it does not.  Both are decidable arithmetic on the pairs,
in the style `MatchingFoldObstruction` established.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

/-! ## 1.  Non-crossing, read through a labelling -/

/-- **A matching is non-crossing when read through `ord`.**  The chord machinery
consumes exactly this: `NonCrossing.card_add_three_le_two_mul_card` asks for
ordered chords that pairwise do not straddle, and asks nothing about how the
labelling relates to the original positions.  So a reordering is admissible
input to the count, which is what makes the folded order worth having. -/
def NonCrossingAt (ord : ℕ → ℕ) (M : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ M, ∀ q ∈ M, ¬ Straddles (ord p.1, ord p.2) (ord q.1, ord q.2)

instance decidableNonCrossingAt (ord : ℕ → ℕ) (M : List (ℕ × ℕ)) :
    Decidable (NonCrossingAt ord M) := by
  unfold NonCrossingAt
  infer_instance

/-! ## 2.  The transfer, as an alternating-path relation -/

/-- **The fold transfer.**  `Transfer mat mir i j` holds when `i` and `j` are
joined by a path that alternates matched and mirror steps, starting and ending
with a matched step.

This is `MatchingFoldObstruction`'s transfer, stated as a relation rather than
computed: that file shows every such path has an odd number of steps and
therefore mutually inverse endpoints, so the relation is a matching of the
relator and boundary letters with no conjugator letter left in it. -/
inductive Transfer (mat mir : ℕ → ℕ → Prop) : ℕ → ℕ → Prop
  | matched {i j : ℕ} : mat i j → Transfer mat mir i j
  | step {i m m' j : ℕ} :
      mat i m → mir m m' → Transfer mat mir m' j → Transfer mat mir i j

/-! ## 3.  Folded planarity -/

/-- The block carried by a position of the labelled word.  The value past the
end is never consumed; it is `Block.boundary` only to keep the function
total. -/
def blockOfPos {α : Type*} [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool)))
    (w : List (α × Bool)) (i : ℕ) : Block :=
  match (labelledWord e w)[i]? with
  | some z => z.2
  | none => Block.boundary

/-- **Folded planarity: the claim the fold has to be replaced by.**

The naive fold asks the transfer to be non-crossing in the original order, and
`MatchingFoldObstruction` refutes that.  This asks only that the transfer be
non-crossing in *some* order, which is all the count needs: the outerplanar
bound `NonCrossing.card_add_three_le_two_mul_card` consumes ordered,
pairwise non-straddling chords and asks nothing about how the labelling relates
to the original positions.

Every hypothesis is written out.  The first four are this lane's standing ones —
the matching is the free-cancellation matching of the labelled word, and the
expression is shortest-then-lightest.  The last five are what `labelledFactor`
makes true of the mirror: it is symmetric and single-valued, it joins the
conjugator block of a factor to the stem block of that same factor, every
conjugator and stem letter has a partner, and two mirror pairs never cross.

The minimality hypothesis cannot be dropped and cannot be weakened to the
metric condition: the two instances in the header satisfy `C'(1/6)` and are
excluded only by minimality.
Whether the *pairwise* form of minimality suffices is open, and is why the
conclusion is stated as an existential rather than with a constructed order —
constructing the order canonically from the matching is the work of proving
this. -/
def FoldedOuterplanar (α : Type*) [DecidableEq α] : Prop :=
  ∀ (R : Set (List (α × Bool))) (e : List (FreeGroup α × List (α × Bool)))
    (w : List (α × Bool)) (T : DTree ((α × Bool) × Block)) (mir : ℕ → ℕ → Prop),
    IsMinimalConjExpr R e (FreeGroup.mk w) →
    FreeGroup.IsReduced w → w ≠ [] →
    T.word = labelledWord e w →
    (∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) →
    (∀ i j, mir i j → mir j i) →
    (∀ i j j', mir i j → mir i j' → j = j') →
    (∀ i j, mir i j → i < j →
      ∃ k, blockOfPos e w i = Block.conj k ∧ blockOfPos e w j = Block.stem k) →
    (∀ i k, blockOfPos e w i = Block.conj k → ∃ j, mir i j) →
    (∀ i k, blockOfPos e w i = Block.stem k → ∃ j, mir i j) →
    (∀ i j k l, mir i j → mir k l → i < j → k < l → ¬ Straddles (i, j) (k, l)) →
    ∃ ord : ℕ → ℕ, ∀ i j k l : ℕ,
      Transfer (fun a b => (a, b) ∈ T.pairIdx) mir i j →
      Transfer (fun a b => (a, b) ∈ T.pairIdx) mir k l →
      ¬ Straddles (ord i, ord j) (ord k, ord l)

/-! ## 4.  The model test, at both instances

The transfers and the folded orders of the two instances in the header, and the
two facts that matter: in the original order the transfer straddles, and in the
folded order it does not.  Both are arithmetic on the pairs, in the style
`MatchingFoldObstruction` established for the obstruction itself. -/

/-- Instance I's transfer: `(0,2)` from the fold, `(1,4)` and `(6,7)` untouched. -/
def transferOne : List (ℕ × ℕ) := [(0, 2), (1, 4), (6, 7)]

/-- Instance I's folded order, `C, B, A, D, E, boundary`. -/
def ordOne : ℕ → ℕ
  | 0 => 0
  | 2 => 1
  | 1 => 2
  | 4 => 3
  | 6 => 4
  | 7 => 5
  | _ => 6

/-- **The obstruction, at Instance I.** -/
theorem transferOne_crosses_identity : ¬ NonCrossingAt id transferOne := by
  decide

/-- **Folded planarity holds at Instance I.**  The same transfer, read in the
order folding induces, has no straddling pair. -/
theorem transferOne_noncrossing_folded : NonCrossingAt ordOne transferOne := by
  decide

/-- Instance II's transfer: `(0,4)` and `(1,3)` from the fold -- `D`'s
conjugator has two letters, so it contributes two transferred pairs -- with
`(2,7)` and `(10,11)` untouched. -/
def transferTwo : List (ℕ × ℕ) := [(0, 4), (1, 3), (2, 7), (10, 11)]

/-- Instance II's folded order, `C, B, A, D, E, boundary` again.  It is constant
on blocks: `0` and `1` are the two letters of `C`, `3` and `4` the two letters of
`B`. -/
def ordTwo : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 3 => 1
  | 4 => 1
  | 2 => 2
  | 7 => 3
  | 10 => 4
  | 11 => 5
  | _ => 6

/-- **The obstruction, at Instance II** -- the instance whose cancelling region
is partial at both ends. -/
theorem transferTwo_crosses_identity : ¬ NonCrossingAt id transferTwo := by
  decide

/-- **Folded planarity holds at Instance II.** -/
theorem transferTwo_noncrossing_folded : NonCrossingAt ordTwo transferTwo := by
  decide

/-- **Both instances, in one statement.**  The naive fold fails at each, and the
same reordering repairs each: neither is a counterexample to
`FoldedOuterplanar`, and neither is repaired by the metric condition or by the
order-blind pairwise lemma. -/
theorem foldedWalk_model_test :
    (¬ NonCrossingAt id transferOne ∧ NonCrossingAt ordOne transferOne) ∧
      (¬ NonCrossingAt id transferTwo ∧ NonCrossingAt ordTwo transferTwo) :=
  ⟨⟨transferOne_crosses_identity, transferOne_noncrossing_folded⟩,
    ⟨transferTwo_crosses_identity, transferTwo_noncrossing_folded⟩⟩

end SmallCancellationRouter
end GroupApproximation
