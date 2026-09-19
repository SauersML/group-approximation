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
of section 6 are the model test: in the identity order the transfer straddles,
in the folded order it does not.  Both are decidable arithmetic on the pairs,
in the style `MatchingFoldObstruction` established.

## Folding does not preserve outerplanarity, and that bounds what can be claimed

The unrestricted claim -- that the fold transfer is non-crossing in *some* order
for every minimal expression -- is **not available**, and the reason is
structural rather than a defect of a particular statement.

The cactus has every letter on its boundary walk, which is why
`MatchingChordGraph` gets non-crossing for free.  The folded object is a genuine
disk diagram, and a disk diagram with an **interior** region -- one meeting no
boundary letter -- has a wheel in its dual: the hub, and the cycle of its
neighbours.  A wheel contains `K₄` as a minor, and no linear order makes the
chords of a `K₄` non-crossing.  So no `ord` exists there.

That is not a corner case.  `one_shell_of_counts` carries the number `s` of
relator blocks meeting no boundary letter as a free variable, and
`CurvatureAssembly`'s header says the seven-runs bound exists precisely for
those blocks.  The `s > 0` branch is the branch the count is built for.

What is *not* claimed: no `C'(1/6)` instance with an interior region has been
built here.  Consecutive neighbours of an interior region meet at a vertex and
need not share an arc, so a wheel is not *forced* by an interior region -- it is
merely not excluded, and it is what an ordinary patch looks like.  The honest
status is that the unrestricted claim is strictly stronger than planarity and
fails for ordinary configurations, not that it is refuted.

## The split this forces, and it is clean

`s = 0` -- every relator block meets the boundary -- is exactly the case with no
enclosed area, since a ring of regions would enclose one, and a simply connected
diagram must fill it with regions that then meet no boundary letter.  So `s = 0`
is exactly the tree-like case, which is exactly where the folded order exists.
The two conditions coincide, which is the sign that the analysis is right rather
than an artefact of the statement.

And the arithmetic follows the same split, both halves proved in section 5:

* at `s = 0` the **outerplanar** bound closes the count outright
  (`one_shell_of_counts_boundary`), so that branch needs only
  `Osin24FactorEdgeBound`'s `hE` and no fold at all on the counting side;
* at `s > 0` the **planar** bound `E ≤ 3V − 6` closes it with no case split
  (`one_shell_of_planar_counts`), and nothing weaker will do.

`FoldedOuterplanarBoundary` is therefore stated for `s = 0` only, and
`FoldedPlanarEdgeBound` names the planar input the other branch needs, so that
the remaining debt of the free gate is two `Prop`s and not a research programme
with no edges.
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

/-- The folded vertex of a position: the factor of its relator block, and
`e.length` for the boundary.  Conjugator and stem letters never occur in the
transfer, so their value is never consumed. -/
def foldedVertex {α : Type*} [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool)))
    (w : List (α × Bool)) (i : ℕ) : ℕ :=
  match blockOfPos e w i with
  | Block.relator k => k
  | _ => e.length

/-- **Folded planarity, at the boundary case.**

The claim the naive fold has to be replaced by, restricted to the case in which
it can hold.  The unrestricted form is not available -- see the header: a disk
diagram with an interior region has a wheel in its dual, and a wheel has no
non-crossing linear layout -- so the last hypothesis asks that every relator
block meet the boundary, which is exactly the tree-like case.

Every other hypothesis is written out too.  The first four are this lane's
standing ones: the matching is the free-cancellation matching of the labelled
word, and the expression is shortest-then-lightest.  The six on `mir` are what
`labelledFactor` makes true of the mirror -- symmetric, single-valued, joining
the conjugator block of a factor to the stem block of that same factor, every
conjugator and stem letter has a partner, and two mirror pairs never cross --
and `hM` says `M` lists the transfer.

The minimality hypothesis cannot be dropped and cannot be weakened to the metric
condition: the two instances in the header satisfy `C'(1/6)` and are excluded
only by minimality.  The conclusion is an existential rather than a constructed
order because constructing the order canonically from the matching IS the
proof. -/
def FoldedOuterplanarBoundary (α : Type*) [DecidableEq α] : Prop :=
  ∀ (R : Set (List (α × Bool))) (e : List (FreeGroup α × List (α × Bool)))
    (w : List (α × Bool)) (T : DTree ((α × Bool) × Block)) (mir : ℕ → ℕ → Prop)
    (M : List (ℕ × ℕ)),
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
    (∀ i j, (i, j) ∈ M ↔ Transfer (fun a b => (a, b) ∈ T.pairIdx) mir i j) →
    (∀ k < e.length, ∃ i j, (i, j) ∈ M ∧
      blockOfPos e w i = Block.relator k ∧ blockOfPos e w j = Block.boundary) →
    ∃ ord : ℕ → ℕ, NonCrossingAt ord M

/-- **The planar input the interior branch needs, named.**

At `s > 0` no order exists and outerplanarity is the wrong tool; what closes the
count there is Euler's bound `E ≤ 3·V − 6` for the folded diagram, which at
`V = e.length + 1` reads `E + 3 ≤ 3·e.length`.  That is this statement, with the
edges counted as the distinct chords the transfer induces on `foldedVertex`, and
it is exactly the shape `one_shell_of_planar_counts` consumes.

This is the whole remaining debt of the interior branch, and it is an
infrastructure debt rather than a small-cancellation one: neither this
repository nor Mathlib has planar graph theory -- no embedding, no Euler
formula -- and the folded diagram is not currently an object at all.  The
repository's existing edge bound, `NonCrossing.card_add_three_le_two_mul_card`,
is the outerplanar one and was proved from scratch for a case where the linear
order is given; here it is not. -/
def FoldedPlanarEdgeBound (α : Type*) [DecidableEq α] : Prop :=
  ∀ (R : Set (List (α × Bool))) (e : List (FreeGroup α × List (α × Bool)))
    (w : List (α × Bool)) (T : DTree ((α × Bool) × Block)) (mir : ℕ → ℕ → Prop)
    (M : List (ℕ × ℕ)),
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
    (∀ i j, (i, j) ∈ M ↔ Transfer (fun a b => (a, b) ∈ T.pairIdx) mir i j) →
    ((M.map fun p =>
        (foldedVertex e w p.1, foldedVertex e w p.2)).toFinset).card + 3
      ≤ 3 * e.length

/-! ## 5.  The count, on both branches

Neither theorem is about folding: they are the arithmetic that says which edge
bound each branch needs, and they are proved.  Together they say the free gate's
remaining debt is exactly one planar bound. -/

/-- **The boundary branch closes on the outerplanar bound alone.**

At `s = 0` -- every relator block meets the boundary -- `one_shell_of_counts`
needs nothing but the edge bound `Osin24FactorEdgeBound` already supplies:
`t = n` and `5·n ≤ dT` give `6·n ≤ 2·e`, hence `e ≥ 3·n`, against `e ≤ 2·n − 1`.
No fold enters the counting side of this branch. -/
theorem one_shell_of_counts_boundary {n t e dT : ℕ}
    (hst : t = n) (hE : e + 1 ≤ 2 * n) (hsum : t + dT = 2 * e)
    (hdT : 5 * t ≤ dT) : False := by
  omega

/-- **The planar bound closes the count with no case split.**

`E ≤ 3·V − 6` at `V = n + 1` is `e + 3 ≤ 3·n`, and then
`6·t + 7·s ≤ 2·e ≤ 6·n − 6 = 6·(s + t) − 6` gives `s + 6 ≤ 0`.  So
`FoldedPlanarEdgeBound` subsumes both branches, and the interior branch needs
nothing beyond it. -/
theorem one_shell_of_planar_counts {n s t e dS dT : ℕ}
    (hst : s + t = n) (hE : e + 3 ≤ 3 * n) (hsum : t + dS + dT = 2 * e)
    (hdS : 7 * s ≤ dS) (hdT : 5 * t ≤ dT) : False := by
  omega

/-! ## 6.  The model test, at both instances

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
`FoldedOuterplanarBoundary`, and neither is repaired by the metric condition or
by the order-blind pairwise lemma.

Both instances have interior relator blocks -- only `E` meets the boundary -- so
they lie in the `s > 0` branch and do not test the boundary case.  What they
test is the reordering itself, which is the part shared by both branches. -/
theorem foldedWalk_model_test :
    (¬ NonCrossingAt id transferOne ∧ NonCrossingAt ordOne transferOne) ∧
      (¬ NonCrossingAt id transferTwo ∧ NonCrossingAt ordTwo transferTwo) :=
  ⟨⟨transferOne_crosses_identity, transferOne_noncrossing_folded⟩,
    ⟨transferTwo_crosses_identity, transferTwo_noncrossing_folded⟩⟩

end SmallCancellationRouter
end GroupApproximation
