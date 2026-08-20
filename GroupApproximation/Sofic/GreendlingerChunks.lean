import GroupApproximation.Sofic.GreendlingerThreeFactor

/-!
# The survivor decomposition of a product of reduced words

`GreendlingerThreeFactor` carries the descent to expressions of any length and
leaves one statement, `LeadingConfinement`: that the block the leading factor
loses stops inside the *next* factor's palindrome.  That statement is not a
consequence of planarity, and it can only be settled by following the block
past the next factor.  This file provides the structure it has to be followed
through.

## What the reduced word of a product looks like

**The reduced word of a product of reduced words is a concatenation of infixes
of the factors, in order.**  Each factor contributes one contiguous *chunk* of
itself --- possibly empty, if the factor is destroyed outright --- and the
chunks appear in the order of the factors.

That is `exists_chunk_decomposition`, and it is unconditional: no minimality, no
small cancellation, nothing about palindromes.  It is proved by the same
induction the descent runs on, with `exists_cancellation_decomposition` at each
step and `dropBlocks` to remove the destroyed prefix from the chunk list without
disturbing the chunk structure.

## What it says about the missing case

A block that outruns the next factor's chunk is matched, letter by letter,
against the chunks after it.  Each chunk is an infix of a palindrome
`c ++ t ++ invRev c`, so the block meets it in at most three segments: a
conjugator segment, a rotation segment, and another conjugator segment.  The
rotation segments are pieces --- common subwords of two symmetrized relators ---
and `C'(1/6)` bounds each by a sixth.  The conjugator segments are hugs, and the
reroute moves of `GreendlingerThreeFactor` bound a hug only against the factor
*adjacent* to it, because the reroute identity moves one factor past its
neighbour and no further.

So the missing content is a bound on a *chain* of such segments along one
rotation, which is what the curvature count over a reduced diagram supplies and
what no single re-expression move can.  This file makes the chain a definable
object instead of an informal picture.

Unconditional throughout.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Dropping letters from the front of a list of blocks -/

/-- The word a list of blocks spells, concatenated in order. -/
def blockWord : List (List (α × Bool)) → List (α × Bool)
  | [] => []
  | A :: L => A ++ blockWord L

@[simp] theorem blockWord_nil :
    blockWord ([] : List (List (α × Bool))) = [] := rfl

@[simp] theorem blockWord_cons (A : List (α × Bool))
    (L : List (List (α × Bool))) :
    blockWord (A :: L) = A ++ blockWord L := rfl

/-- Removing the first `n` letters of the word a block list spells, without
disturbing the block structure: the blocks it eats become empty, and the block
it stops inside loses a prefix. -/
def dropBlocks : ℕ → List (List (α × Bool)) → List (List (α × Bool))
  | _, [] => []
  | n, A :: L =>
      if n ≤ A.length then A.drop n :: L else [] :: dropBlocks (n - A.length) L

/-! ## Two facts about dropping past a concatenation -/

/-- Dropping fewer letters than the first block has leaves the second block
untouched. -/
theorem drop_append_of_le {β : Type*} :
    ∀ (n : ℕ) (l₁ l₂ : List β), n ≤ l₁.length →
      (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  intro n
  induction n with
  | zero =>
      intro l₁ l₂ _
      simp
  | succ n ih =>
      intro l₁ l₂ h
      cases l₁ with
      | nil =>
          rw [List.length_nil] at h
          exact absurd h (by omega)
      | cons x xs =>
          rw [List.length_cons] at h
          simp only [List.cons_append, List.drop_succ_cons]
          exact ih xs l₂ (by omega)

/-- Dropping at least as many letters as the first block has consumes it whole.
-/
theorem drop_append_of_ge {β : Type*} :
    ∀ (l₁ : List β) (n : ℕ) (l₂ : List β), l₁.length ≤ n →
      (l₁ ++ l₂).drop n = l₂.drop (n - l₁.length) := by
  intro l₁
  induction l₁ with
  | nil =>
      intro n l₂ _
      simp
  | cons x xs ih =>
      intro n l₂ h
      cases n with
      | zero =>
          rw [List.length_cons] at h
          exact absurd h (by omega)
      | succ m =>
          rw [List.length_cons] at h
          simp only [List.cons_append, List.drop_succ_cons, List.length_cons]
          rw [ih m l₂ (by omega)]
          congr 1
          omega

/-- `dropBlocks` does to the block list what `drop` does to the word. -/
theorem blockWord_dropBlocks :
    ∀ (C : List (List (α × Bool))) (n : ℕ),
      blockWord (dropBlocks n C) = (blockWord C).drop n := by
  intro C
  induction C with
  | nil =>
      intro n
      simp [dropBlocks]
  | cons A L ih =>
      intro n
      rw [dropBlocks]
      split_ifs with h
      · rw [blockWord_cons, blockWord_cons, drop_append_of_le n A (blockWord L) h]
      · rw [blockWord_cons, blockWord_cons, List.nil_append, ih (n - A.length),
          drop_append_of_ge A n (blockWord L) (by omega)]

/-! ## The chunks are infixes -/

/-- Every block list refines itself. -/
theorem forall₂_infix_refl :
    ∀ L : List (List (α × Bool)),
      List.Forall₂ (fun x y => x <:+: y) L L := by
  intro L
  induction L with
  | nil => exact List.Forall₂.nil
  | cons A L ih => exact List.Forall₂.cons (List.infix_refl A) ih

/-- Refinement is transitive, because infixes are. -/
theorem forall₂_infix_trans :
    ∀ {A B C : List (List (α × Bool))},
      List.Forall₂ (fun x y => x <:+: y) A B →
        List.Forall₂ (fun x y => x <:+: y) B C →
          List.Forall₂ (fun x y => x <:+: y) A C := by
  intro A B C h₁
  induction h₁ generalizing C with
  | nil =>
      intro h₂
      cases h₂
      exact List.Forall₂.nil
  | cons hab _ ih =>
      intro h₂
      cases h₂ with
      | cons hbc hBC => exact List.Forall₂.cons (hab.trans hbc) (ih hBC)

/-- Dropping letters refines the block list: each block loses a prefix, or all
of itself. -/
theorem dropBlocks_forall₂ :
    ∀ (C : List (List (α × Bool))) (n : ℕ),
      List.Forall₂ (fun x y => x <:+: y) (dropBlocks n C) C := by
  intro C
  induction C with
  | nil =>
      intro n
      rw [dropBlocks]
      exact List.Forall₂.nil
  | cons A L ih =>
      intro n
      rw [dropBlocks]
      split_ifs with h
      · exact List.Forall₂.cons (List.drop_suffix n A).isInfix (forall₂_infix_refl L)
      · exact List.Forall₂.cons List.nil_infix (ih (n - A.length))

/-! ## The survivor decomposition -/

/-- **The reduced word of a product of reduced words is a concatenation of
infixes of the factors, in order.**  Each factor contributes one contiguous
chunk of itself, possibly empty; the chunks keep the order of the factors.

Unconditional: no minimality, no small cancellation, no palindromes.  This is
the structure a cancellation block travels through when it outruns the factor
next to it, and so the frame in which the descent's remaining case has to be
stated. -/
theorem exists_chunk_decomposition :
    ∀ (L : List (List (α × Bool))), (∀ A ∈ L, FreeGroup.IsReduced A) →
      ∃ C : List (List (α × Bool)),
        List.Forall₂ (fun x y => x <:+: y) C L ∧
          FreeGroup.IsReduced (blockWord C) ∧
          FreeGroup.mk (blockWord C) = FreeGroup.mk (blockWord L) := by
  intro L
  induction L with
  | nil =>
      intro _
      exact ⟨[], List.Forall₂.nil, by rw [blockWord_nil]; exact FreeGroup.IsReduced.nil,
        rfl⟩
  | cons A L ih =>
      intro hred
      obtain ⟨C, hCL, hCred, hCmk⟩ :=
        ih fun B hB => hred B (List.mem_cons_of_mem A hB)
      have hA : FreeGroup.IsReduced A := hred A List.mem_cons_self
      obtain ⟨A', M, B', h1, h2, h3, h4⟩ :=
        exists_cancellation_decomposition (blockWord C) hCred A hA
      have hdrop : (blockWord C).drop M.length = B' := by
        rw [h2, drop_append_of_ge (FreeGroup.invRev M) M.length B'
          (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
          Nat.sub_self, List.drop_zero]
      have hword : blockWord (A' :: dropBlocks M.length C) = A' ++ B' := by
        rw [blockWord_cons, blockWord_dropBlocks, hdrop]
      refine ⟨A' :: dropBlocks M.length C, ?_, ?_, ?_⟩
      · refine List.Forall₂.cons ?_
          (forall₂_infix_trans (dropBlocks_forall₂ C M.length) hCL)
        exact ⟨[], M, by rw [h1]; simp⟩
      · rw [hword]
        exact h3
      · calc
          FreeGroup.mk (blockWord (A' :: dropBlocks M.length C))
              = FreeGroup.mk (A' ++ B') := congrArg FreeGroup.mk hword
          _ = FreeGroup.mk A * FreeGroup.mk (blockWord C) := h4.symm
          _ = FreeGroup.mk A * FreeGroup.mk (blockWord L) :=
            congrArg (FreeGroup.mk A * ·) hCmk
          _ = FreeGroup.mk (A ++ blockWord L) := FreeGroup.mul_mk
          _ = FreeGroup.mk (blockWord (A :: L)) := rfl

/-! ## The arithmetic of an overrun -/

/-- **A block that overruns leaves the next factor keeping at most two thirds.**
To overrun, the block must cover the whole surviving stretch `m` of the next
rotation, and it covers it with a hug --- at most half the rotation, by
`hug_le_of_minimal_reroute` --- followed by a piece, under a sixth by `C'(1/6)`.
-/
theorem survivor_le_of_overrun {m q p T : ℕ}
    (hcover : m = q + p) (hhug : 2 * q ≤ T) (hpiece : 6 * p < T) :
    3 * m ≤ 2 * T := by
  omega

/-- **A block that overruns eats only two pieces**, so its own factor keeps more
than two thirds of its rotation: past the next factor the block lands among
relator letters, so both segments are pieces. -/
theorem survivor_gt_of_two_pieces {m E p D T : ℕ}
    (hkeep : m + E = T) (hsplit : E = p + D)
    (hp : 6 * p < T) (hD : 6 * D < T) :
    2 * T < 3 * m := by
  omega

/-- **Overruns cannot occur at two consecutive levels.**  One forces the next
factor's survivor to at most two thirds of its rotation, the other forces it
above two thirds.

This is the sharpest structural fact the descent has about the configuration
`GreendlingerThreeFactor.LeadingConfinement` still carries, and it is what a
continuation should induct on: the remaining case is a block that overruns and
then exhausts the chunk it lands in, reaching the conjugator of a factor it is
not adjacent to. -/
theorem not_consecutive_overrun {m q p E p' D T : ℕ}
    (hcover : m = q + p) (hhug : 2 * q ≤ T) (hpiece : 6 * p < T)
    (hkeep : m + E = T) (hsplit : E = p' + D)
    (hp' : 6 * p' < T) (hD : 6 * D < T) (_ : 0 < T) : False := by
  omega

end SmallCancellationRouter
end GroupApproximation
