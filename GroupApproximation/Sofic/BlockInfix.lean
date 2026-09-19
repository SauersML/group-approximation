import GroupApproximation.Sofic.ConjExprMatching

/-!
# A run that stays in one block is a subword of that block

`MatchingSpine` shows that a run of the cancellation matching brackets its word
as a conjugate `F ++ (core ++ invRev F)`.  To turn that into a *piece* bound one
more step is needed: if every letter of `F` carries the same label, then `F` is a
contiguous subword of the block that label names --- so a run joining two relator
blocks exhibits one and the same word inside two relators, which is exactly what
`C'(1/6)` measures.

The argument is pure list surgery and needs nothing about free groups.  A
stretch all of whose letters are labelled `b` cannot poke out of the `b`-block on
either side, because the letters immediately outside carry other labels:

* `infix_of_forall_ne_left` --- it cannot start early;
* `infix_of_forall_ne_right` --- and by reversal, it cannot end late;
* `map_fst_infix_of_label` --- so it lies inside the tagged block, and forgetting
  the labels puts it inside the block's own word.

Unconditional.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## A uniformly labelled stretch cannot leave its block -/

/-- **It cannot start early.**  If every letter of `L` is labelled `b` and no
letter of `X` is, then an occurrence of `L` in `X ++ Y` is an occurrence in `Y`. -/
theorem infix_of_forall_ne_left {b : Block} {L : List ((α × Bool) × Block)} :
    ∀ X Y : List ((α × Bool) × Block), (∀ p ∈ L, p.2 = b) → (∀ p ∈ X, p.2 ≠ b) →
      L <:+: X ++ Y → L <:+: Y := by
  intro X
  induction X with
  | nil =>
      intro Y _ _ h
      rwa [List.nil_append] at h
  | cons x X' ih =>
      intro Y hL hX h
      obtain ⟨P, S, hPS⟩ := h
      rcases P with _ | ⟨p, P'⟩
      · rw [List.nil_append, List.cons_append] at hPS
        rcases L with _ | ⟨l, L'⟩
        · exact ⟨[], Y, by simp⟩
        · exfalso
          rw [List.cons_append] at hPS
          simp only [List.cons.injEq] at hPS
          have hlx : l = x := hPS.1
          have hlb : l.2 = b := hL l (by simp)
          exact hX x (by simp) (by rw [← hlx]; exact hlb)
      · rw [List.cons_append, List.cons_append] at hPS
        refine ih Y hL (fun q hq => hX q (by simp [hq])) ⟨P', S, ?_⟩
        exact (List.cons.inj hPS).2

/-- **It cannot end late**, by the same argument read backwards. -/
theorem infix_of_forall_ne_right {b : Block} {L X Y : List ((α × Bool) × Block)}
    (hL : ∀ p ∈ L, p.2 = b) (hY : ∀ p ∈ Y, p.2 ≠ b) (h : L <:+: X ++ Y) :
    L <:+: X := by
  have hrev : L.reverse <:+: Y.reverse ++ X.reverse := by
    rw [← List.reverse_append]
    exact List.reverse_infix.mpr h
  have hLrev : ∀ p ∈ L.reverse, p.2 = b := by
    intro p hp
    exact hL p (List.mem_reverse.mp hp)
  have hYrev : ∀ p ∈ Y.reverse, p.2 ≠ b := by
    intro p hp
    exact hY p (List.mem_reverse.mp hp)
  have hfin := infix_of_forall_ne_left Y.reverse X.reverse hLrev hYrev hrev
  exact List.reverse_infix.mp hfin

/-! ## Forgetting the labels -/

/-- An occurrence inside a labelled list is an occurrence inside its letters. -/
theorem map_fst_infix {L M : List ((α × Bool) × Block)} (h : L <:+: M) :
    L.map Prod.fst <:+: M.map Prod.fst := by
  obtain ⟨P, S, hPS⟩ := h
  refine ⟨P.map Prod.fst, S.map Prod.fst, ?_⟩
  rw [← List.map_append, ← List.map_append, hPS]

/-- **A run that stays in one block is a subword of that block.**  If `L` is a
contiguous stretch of the labelled word, every letter of it carries the label of
the block `tag b t`, and no letter outside that block carries it, then the
letters of `L` form a contiguous subword of `t`. -/
theorem map_fst_infix_of_label {b : Block} {t : List (α × Bool)}
    {L X Y : List ((α × Bool) × Block)}
    (hL : ∀ p ∈ L, p.2 = b) (hX : ∀ p ∈ X, p.2 ≠ b) (hY : ∀ p ∈ Y, p.2 ≠ b)
    (h : L <:+: X ++ (tag b t ++ Y)) :
    L.map Prod.fst <:+: t := by
  have h1 : L <:+: tag b t ++ Y := infix_of_forall_ne_left X (tag b t ++ Y) hL hX h
  have h2 : L <:+: tag b t := infix_of_forall_ne_right hL hY h1
  have h3 := map_fst_infix h2
  rwa [map_fst_tag] at h3

/-! ## The labels of the blocks are what they should be -/

/-- Every letter of a tagged block carries its tag. -/
theorem forall_mem_tag (b : Block) (l : List (α × Bool)) :
    ∀ p ∈ tag b l, p.2 = b := by
  intro p hp
  rw [tag, List.mem_map] at hp
  obtain ⟨x, -, rfl⟩ := hp
  rfl

/-- Every letter of a labelled factor carries one of that factor's three labels. -/
theorem forall_mem_labelledFactor (k : ℕ) (c s : List (α × Bool)) :
    ∀ p ∈ labelledFactor k c s,
      p.2 = Block.conj k ∨ p.2 = Block.relator k ∨ p.2 = Block.stem k := by
  intro p hp
  rw [labelledFactor, List.mem_append] at hp
  rcases hp with hp | hp
  · exact Or.inl (forall_mem_tag _ _ p hp)
  · rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact Or.inr (Or.inl (forall_mem_tag _ _ p hp))
    · exact Or.inr (Or.inr (forall_mem_tag _ _ p hp))

/-- Every letter of a labelled expression carries a label whose factor index lies
in the half-open interval occupied by that expression.  This is what keeps the
blocks of distinct factors apart. -/
theorem index_mem_range_of_mem_labelledExpr [DecidableEq α] :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool)))
      (p : (α × Bool) × Block), p ∈ labelledExpr k e →
      (∃ j, k ≤ j ∧ j < k + e.length ∧
        (p.2 = Block.conj j ∨ p.2 = Block.relator j ∨
        p.2 = Block.stem j)) := by
  intro k e
  induction e generalizing k with
  | nil =>
      intro p hp
      exact absurd hp (by simp)
  | cons xs e ih =>
      obtain ⟨x, s⟩ := xs
      intro p hp
      rw [labelledExpr_cons, List.mem_append] at hp
      rcases hp with hp | hp
      · exact ⟨k, le_rfl, by simp, forall_mem_labelledFactor k x.toWord s p hp⟩
      · obtain ⟨j, hj, hjlt, hlab⟩ := ih (k + 1) p hp
        exact ⟨j, by omega, by simp only [List.length_cons]; omega, hlab⟩

/-- No letter of a labelled expression is a boundary letter. -/
theorem ne_boundary_of_mem_labelledExpr [DecidableEq α]
    (k : ℕ) (e : List (FreeGroup α × List (α × Bool)))
    (p : (α × Bool) × Block) (hp : p ∈ labelledExpr k e) :
    p.2 ≠ Block.boundary := by
  obtain ⟨j, -, -, hlab⟩ := index_mem_range_of_mem_labelledExpr k e p hp
  rcases hlab with h | h | h <;> rw [h] <;> exact Block.noConfusion

end SmallCancellationRouter
end GroupApproximation
