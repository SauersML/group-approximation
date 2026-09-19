import GroupApproximation.GGT.HullSCRelatorSeparationLetters

/-!
# Step (b): a matched block fixes the rotation

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, §6, after
Olshanskii.

Once the blocks of two matched prefixes are aligned with equal exponents, the
alignment has to become an equality of *words*.  It does, and the reason is
positional: a block letter of the relator occurs at exactly one position
(`blockPosition_unique`, from `HullSC.nodup_blockLetters` and
`HullSC.notMem_map_base_of_comp`), so two rotations carrying the same block
letter at the same offset are rotations by the same amount, hence equal.

`rotate_eq_of_block_at_offset` is that statement, and it is what closes the case
of Olshanskii's step (c) in which both members of the symmetrized closure are
rotations of the relator itself: it makes them the same word, which the
corrected separation excludes by `w' ≠ w`.

The four private lemmas are list facts stated in the `getElem?` form the
argument uses; `List.mem_of_getElem?`, `List.getElem?_append_left`,
`List.getElem?_append_right`, `List.getElem?_rotate`, `List.rotate_mod`,
`List.rotate_rotate` and `List.rotate_injective` come from the library.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## List facts, in the `getElem?` form -/

/-- In a list without repetition an entry determines its position. -/
private theorem eq_of_getElem?_eq_of_nodup {α : Type v} :
    ∀ {l : List α}, l.Nodup → ∀ {i j : ℕ} {x : α},
      l[i]? = some x → l[j]? = some x → i = j := by
  intro l
  induction l with
  | nil =>
      intro _ _ _ _ hi _
      simp at hi
  | cons b t ih =>
      intro hnd i j x hi hj
      rw [List.nodup_cons] at hnd
      cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j' =>
              rw [List.getElem?_cons_zero] at hi
              rw [List.getElem?_cons_succ] at hj
              refine absurd ?_ hnd.1
              rw [Option.some.inj hi]
              exact List.mem_of_getElem? hj
      | succ i' =>
          cases j with
          | zero =>
              rw [List.getElem?_cons_zero] at hj
              rw [List.getElem?_cons_succ] at hi
              refine absurd ?_ hnd.1
              rw [Option.some.inj hj]
              exact List.mem_of_getElem? hi
          | succ j' =>
              rw [List.getElem?_cons_succ] at hi
              rw [List.getElem?_cons_succ] at hj
              have hij := ih hnd.2 hi hj
              omega

/-- An entry of a concatenation that misses the first part and does not repeat
in the second determines its position. -/
private theorem eq_of_getElem?_append_eq {α : Type v} {l₁ l₂ : List α} {x : α}
    (hnd : l₂.Nodup) (hx : x ∉ l₁) {q q' : ℕ}
    (h : (l₁ ++ l₂)[q]? = some x) (h' : (l₁ ++ l₂)[q']? = some x) : q = q' := by
  have key : ∀ r : ℕ, (l₁ ++ l₂)[r]? = some x →
      l₁.length ≤ r ∧ l₂[r - l₁.length]? = some x := by
    intro r hr
    rcases Nat.lt_or_ge r l₁.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hr
      exact absurd (List.mem_of_getElem? hr) hx
    · exact ⟨hge, by rwa [List.getElem?_append_right hge] at hr⟩
  obtain ⟨hq, hq2⟩ := key q h
  obtain ⟨hq', hq'2⟩ := key q' h'
  have hsub := eq_of_getElem?_eq_of_nodup hnd hq2 hq'2
  omega

/-- The first letter of a rotation. -/
private theorem getElem?_zero_rotate {α : Type v} {l : List α}
    (hl : 0 < l.length) (e : ℕ) :
    (l.rotate e)[0]? = l[e % l.length]? := by
  rw [List.getElem?_rotate hl, Nat.zero_add]

/-- Reading a rotation at an offset is reading a further rotation at its
start. -/
private theorem getElem?_rotate_shift {α : Type v} {l : List α} {c d : ℕ}
    (hd : d < l.length) : (l.rotate c)[d]? = (l.rotate (c + d))[0]? := by
  rw [List.getElem?_rotate hd,
    getElem?_zero_rotate (Nat.lt_of_le_of_lt (Nat.zero_le d) hd), Nat.add_comm c d]

/-- A common further rotation can be cancelled. -/
private theorem rotate_eq_of_rotate_add_eq {α : Type v} {l : List α} {c c' d : ℕ}
    (h : l.rotate (c + d) = l.rotate (c' + d)) : l.rotate c = l.rotate c' := by
  rw [← List.rotate_rotate, ← List.rotate_rotate] at h
  exact List.rotate_injective d h

/-! ## Blocks fix the rotation -/

section Rotation

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **A block letter of the relator occurs at exactly one position.**  It is not
a letter of the base part (`notMem_map_base_of_comp`) and the block part has no
repetition (`nodup_blockLetters`). -/
theorem blockPosition_unique (E : HypEmbeddedCore A N) {p : List G} {ms : List ℕ}
    (hnodup : ms.Nodup) {q q' m : ℕ}
    (hq : (relatorWord p E.lox ms)[q]?
      = some (GGT.RelLetter.comp () (E.lox ^ m)))
    (hq' : (relatorWord p E.lox ms)[q']?
      = some (GGT.RelLetter.comp () (E.lox ^ m))) : q = q' := by
  have hv : relatorWord p E.lox ms
      = p.map GGT.RelLetter.base
        ++ ms.map (fun r => GGT.RelLetter.comp () (E.lox ^ r)) := rfl
  rw [hv] at hq hq'
  exact eq_of_getElem?_append_eq (nodup_blockLetters E hnodup)
    (notMem_map_base_of_comp p () (E.lox ^ m)) hq hq'

/-- **Two rotations of the relator carrying the same block letter at the same
offset are equal.**

This is Olshanskii's step from "the blocks correspond" to "the two words are the
same": the block letter names its own position, so the two rotation indices are
congruent modulo the length, so the two rotations are the same list.

In the corrected separation this closes the case where `w` and `w'` are both
rotations of the relator: it contradicts `w' ≠ w`, and no further geometry is
spent. -/
theorem rotate_eq_of_block_at_offset (E : HypEmbeddedCore A N) {p : List G}
    {ms : List ℕ} (hnodup : ms.Nodup) {c c' d m : ℕ}
    (hd : d < (relatorWord p E.lox ms).length)
    (he : ((relatorWord p E.lox ms).rotate c)[d]?
      = some (GGT.RelLetter.comp () (E.lox ^ m)))
    (he' : ((relatorWord p E.lox ms).rotate c')[d]?
      = some (GGT.RelLetter.comp () (E.lox ^ m))) :
    (relatorWord p E.lox ms).rotate c = (relatorWord p E.lox ms).rotate c' := by
  have hl : 0 < (relatorWord p E.lox ms).length :=
    Nat.lt_of_le_of_lt (Nat.zero_le d) hd
  rw [getElem?_rotate_shift hd, getElem?_zero_rotate hl] at he
  rw [getElem?_rotate_shift hd, getElem?_zero_rotate hl] at he'
  have hmod : (c + d) % (relatorWord p E.lox ms).length
      = (c' + d) % (relatorWord p E.lox ms).length :=
    blockPosition_unique E hnodup he he'
  refine rotate_eq_of_rotate_add_eq (d := d) ?_
  rw [← List.rotate_mod (relatorWord p E.lox ms) (c + d),
    ← List.rotate_mod (relatorWord p E.lox ms) (c' + d), hmod]

end Rotation

end HullSC
end GroupApproximation
