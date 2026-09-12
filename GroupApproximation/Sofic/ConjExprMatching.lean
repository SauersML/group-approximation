import GroupApproximation.Sofic.MatchingSpine

/-!
# The matching of a conjugate-product expression, with its blocks named

`NonCrossingMatching` says the cancellation of a word that dies is carried by a
`DTree`, and that the tree lifts to a *labelled* word.  This file supplies the
labels for the word that matters: the one a conjugate-product expression spells,
followed by the formal inverse of the reduced word it reduces to.

  `labelledWord e w = c₁ t₁ c₁⁻¹ c₂ t₂ c₂⁻¹ ⋯ cₙ tₙ cₙ⁻¹ · w⁻¹`

with every letter tagged by the block it came from: `conj k` and `stem k` for the
two copies of the `k`-th conjugator, `relator k` for the `k`-th relator, and
`boundary` for the letters of `w⁻¹`.

## What the labels are for

Each matched pair of the tree joins two blocks, and which two decides what the
pair *is* in the diagram the expression describes:

* `relator k` ↔ `boundary` --- a letter of a relator that survives into `w`.
  These are the boundary edges, and there are exactly `|w|` of them.
* `relator k` ↔ `relator l` --- two relators cancelling against each other.  A
  maximal run of these is an interior edge, and `MatchingSpine` shows a run makes
  a common subword of the two relators, which is what `C'(1/6)` bounds.
* anything ↔ `conj`/`stem` --- the stems of the cactus, the part of the picture a
  reduced diagram does not have.

So the whole curvature count is a statement about how many pairs of each kind a
tree over `labelledWord e w` can have, and the labels are what make that
countable.

Unconditional: this file builds the object, and asserts nothing about small
cancellation.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Blocks -/

/-- Where a letter of the expression's word came from. -/
inductive Block where
  | conj (k : ℕ) : Block
  | relator (k : ℕ) : Block
  | stem (k : ℕ) : Block
  | boundary : Block
  deriving DecidableEq

/-- Is this letter part of a relator? -/
def Block.isRelator : Block → Bool
  | relator _ => true
  | _ => false

/-- Is this letter part of the boundary? -/
def Block.isBoundary : Block → Bool
  | boundary => true
  | _ => false

/-! ## The labelled word -/

/-- Tagging a word with one block. -/
def tag (b : Block) (l : List (α × Bool)) : List ((α × Bool) × Block) :=
  l.map (fun x => (x, b))

@[simp] theorem map_fst_tag (b : Block) (l : List (α × Bool)) :
    (tag b l).map Prod.fst = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change x :: (tag b l).map Prod.fst = x :: l
      rw [ih]

@[simp] theorem length_tag (b : Block) (l : List (α × Bool)) :
    (tag b l).length = l.length := by
  rw [tag, List.length_map]

/-- One factor of the expression, labelled: the conjugator, the relator, the
inverted conjugator. -/
def labelledFactor (k : ℕ) (c s : List (α × Bool)) : List ((α × Bool) × Block) :=
  tag (Block.conj k) c
    ++ (tag (Block.relator k) s ++ tag (Block.stem k) (FreeGroup.invRev c))

@[simp] theorem map_fst_labelledFactor (k : ℕ) (c s : List (α × Bool)) :
    (labelledFactor k c s).map Prod.fst = c ++ (s ++ FreeGroup.invRev c) := by
  rw [labelledFactor, List.map_append, List.map_append, map_fst_tag, map_fst_tag,
    map_fst_tag]

/-- The whole expression, labelled, starting the factor count at `k`. -/
def labelledExpr [DecidableEq α] :
    ℕ → List (FreeGroup α × List (α × Bool)) → List ((α × Bool) × Block)
  | _, [] => []
  | k, (x, s) :: e => labelledFactor k x.toWord s ++ labelledExpr (k + 1) e

@[simp] theorem labelledExpr_nil [DecidableEq α] (k : ℕ) :
    labelledExpr k ([] : List (FreeGroup α × List (α × Bool))) = [] := rfl

@[simp] theorem labelledExpr_cons [DecidableEq α] (k : ℕ) (x : FreeGroup α)
    (s : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool))) :
    labelledExpr k ((x, s) :: e)
      = labelledFactor k x.toWord s ++ labelledExpr (k + 1) e := rfl

/-- **The labels forget to the expression's word.** -/
theorem map_fst_labelledExpr [DecidableEq α] :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool))),
      (labelledExpr k e).map Prod.fst = exprWord e := by
  intro k e
  induction e generalizing k with
  | nil => rfl
  | cons xs e ih =>
      obtain ⟨x, s⟩ := xs
      rw [labelledExpr_cons, List.map_append, map_fst_labelledFactor, exprWord_cons,
        ih (k + 1)]

/-- The expression's word followed by the inverse of what it reduces to, with
every letter labelled by its block. -/
def labelledWord [DecidableEq α] (e : List (FreeGroup α × List (α × Bool)))
    (w : List (α × Bool)) : List ((α × Bool) × Block) :=
  labelledExpr 0 e ++ tag Block.boundary (FreeGroup.invRev w)

/-- **The labels forget to the word whose cancellation we are counting.** -/
theorem map_fst_labelledWord [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) :
    (labelledWord e w).map Prod.fst = exprWord e ++ FreeGroup.invRev w := by
  rw [labelledWord, List.map_append, map_fst_labelledExpr, map_fst_tag]

/-- **That word dies**, which is the whole reason it has a matching: the
expression spells what `w` spells, so the two cancel. -/
theorem mk_map_fst_labelledWord [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (h : conjEval e = FreeGroup.mk w) :
    FreeGroup.mk ((labelledWord e w).map Prod.fst) = 1 := by
  rw [map_fst_labelledWord, mk_append_mul, mk_invRev_eq_inv, mk_exprWord, h]
  group

/-! ## The matching, with blocks attached -/

/-- **Every conjugate-product expression carries a labelled matching.**  This is
the object the curvature count runs on: a non-crossing perfect matching of the
letters of `c₁t₁c₁⁻¹ ⋯ cₙtₙcₙ⁻¹ w⁻¹` in which every matched pair knows which two
blocks it joins. -/
theorem exists_dtree_labelledWord [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (h : conjEval e = FreeGroup.mk w) :
    ∃ T : DTree ((α × Bool) × Block), T.word = labelledWord e w ∧
      ∀ p ∈ T.pairs, (p.2).1 = invLetter (p.1).1 :=
  exists_dtree_of_dyck_map Prod.fst (labelledWord e w).length (labelledWord e w)
    le_rfl (mk_map_fst_labelledWord h)

/-- The boundary block has exactly the letters of `w`. -/
@[simp] theorem length_tag_boundary [DecidableEq α] (w : List (α × Bool)) :
    (tag Block.boundary (FreeGroup.invRev w)).length = w.length := by
  rw [length_tag, FreeGroup.invRev_length]

end SmallCancellationRouter
end GroupApproximation
