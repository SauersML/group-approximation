import GroupApproximation.GGT.HullSCRelatorSeparation2Rotation

/-!
# Step (c), first half: the formal inverse names its positions too

`HullSC.RelWord.Sym.exists_rotate` splits the symmetrized closure of the
alternating relator into the rotations of the relator and the rotations of its
formal inverse, so Olshanskii's step (c) has four cases.  Step (b)
(`GGT/HullSCRelatorSeparation2Rotation.lean`) closes the case where both members
are rotations of the relator.  This module closes the case where both are
rotations of the formal inverse, by the same argument on the mirrored word.

Two things have to be redone rather than reused, and both are the same
asymmetry: formal inversion reverses the concatenation, so in
`revInv (relatorWord₂ p h₀ h₁ ms)` the run comes **first** and the base part
last.

* `getElem?_append_index_eq_left` is the dual of
  `HullSC.getElem?_append_index_eq`: the distinguished letter now misses the
  *second* part of the concatenation and does not repeat in the first.
* `nodup_revInv` and `notMem_revInv_map_base_of_comp` transport the two
  properties of the run and of the base part across formal inversion.  Neither
  needs a new hypothesis: inversion of letters is an involution, hence
  injective, and the formal inverse of a base letter is a base letter.

`rotate_eq_of_position_unique` is the rotation argument of step (b) with the
uniqueness of the position taken as a hypothesis, so that the two halves share
it instead of repeating it.

What is left of step (c) after this module is the genuinely mixed case: one
member a rotation of the relator, the other a rotation of its formal inverse.
That case is not a matter of positions -- the two words are never equal -- and
is treated separately.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-! ## Reading a concatenation whose distinguished letter is in the first part -/

/-- An entry of a concatenation that misses the second part and does not repeat
in the first determines its position.  The dual of
`HullSC.getElem?_append_index_eq`, and the form the mirrored relator needs. -/
theorem getElem?_append_index_eq_left {α : Type v} {l₁ l₂ : List α} {x : α}
    (hnd : l₁.Nodup) (hx : x ∉ l₂) {q q' : ℕ}
    (h : (l₁ ++ l₂)[q]? = some x) (h' : (l₁ ++ l₂)[q']? = some x) : q = q' := by
  have key : ∀ r : ℕ, (l₁ ++ l₂)[r]? = some x → l₁[r]? = some x := by
    intro r hr
    rcases Nat.lt_or_ge r l₁.length with hlt | hge
    · rwa [List.getElem?_append_left hlt] at hr
    · rw [List.getElem?_append_right hge] at hr
      exact absurd (List.mem_of_getElem? hr) hx
  exact getElem?_eq_of_nodup hnd (key q h) (key q' h')

/-- The rotation argument of step (b), with the uniqueness of the position of
the distinguished letter taken as a hypothesis: reading two rotations at a
common offset and finding the same letter makes the two rotation indices
congruent modulo the length, so the two rotations are the same list. -/
theorem rotate_eq_of_position_unique {α : Type v} {l : List α} {x : α}
    (huniq : ∀ q q' : ℕ, l[q]? = some x → l[q']? = some x → q = q')
    {c c' d : ℕ} (hd : d < l.length)
    (he : (l.rotate c)[d]? = some x) (he' : (l.rotate c')[d]? = some x) :
    l.rotate c = l.rotate c' := by
  have hl : 0 < l.length := Nat.lt_of_le_of_lt (Nat.zero_le d) hd
  rw [getElem?_rotate_at hd, getElem?_rotate_head hl] at he
  rw [getElem?_rotate_at hd, getElem?_rotate_head hl] at he'
  have hmod : (c + d) % l.length = (c' + d) % l.length := huniq _ _ he he'
  refine rotate_cancel_right (d := d) ?_
  rw [← List.rotate_mod l (c + d), ← List.rotate_mod l (c' + d), hmod]

/-! ## Formal inversion preserves what the argument needs -/

section Mirror

variable {G : Type u} [Group G] {Λ : Type w}

/-- Inversion of letters is an involution, so it is injective. -/
theorem injective_relLetter_inv :
    Function.Injective (RelWord.inv (G := G) (Λ := Λ)) := by
  intro a a' haa
  have h : RelWord.inv (RelWord.inv a) = RelWord.inv (RelWord.inv a') := by
    rw [haa]
  rwa [RelWord.inv_inv_letter, RelWord.inv_inv_letter] at h

/-- **The formal inverse of a repetition-free word is repetition-free.** -/
theorem nodup_revInv {l : List (GGT.RelLetter G Λ)} (h : l.Nodup) :
    (RelWord.revInv l).Nodup := by
  show ((l.map RelWord.inv).reverse).Nodup
  exact List.nodup_reverse.mpr (List.Nodup.map injective_relLetter_inv h)

/-- **The formal inverse of the base part contains no block letter.**  A letter
of a formal inverse is the formal inverse of a letter, and the formal inverse of
a block letter is a block letter. -/
theorem notMem_revInv_map_base_of_comp (l : List G) (lam : Λ) (h : G) :
    (GGT.RelLetter.comp lam h : GGT.RelLetter G Λ)
      ∉ RelWord.revInv (l.map GGT.RelLetter.base) := by
  intro hmem
  have hinv : (GGT.RelLetter.comp lam h⁻¹ : GGT.RelLetter G Λ)
      ∈ l.map GGT.RelLetter.base := RelWord.inv_mem_of_mem_revInv hmem
  exact notMem_map_base_of_comp l lam h⁻¹ hinv

end Mirror

/-! ## The mirrored relator names its positions -/

section MirrorRelator

variable {G : Type u} [Group G]

/-- **The formal inverse of the alternating relator, split.**  Inversion
reverses the concatenation, so the run comes first and the base part last. -/
theorem revInv_relatorWord₂ (p : List G) (h₀ h₁ : G) (ms : List ℕ) :
    RelWord.revInv (relatorWord₂ p h₀ h₁ ms)
      = RelWord.revInv (blockWord h₀ h₁ false ms)
        ++ RelWord.revInv (p.map GGT.RelLetter.base) := by
  show RelWord.revInv (p.map GGT.RelLetter.base ++ blockWord h₀ h₁ false ms)
    = RelWord.revInv (blockWord h₀ h₁ false ms)
      ++ RelWord.revInv (p.map GGT.RelLetter.base)
  rw [RelWord.revInv_append]

/-- **A block letter of the mirrored relator occurs at exactly one position.**
`HullSC.blockPosition_unique₂` on the other side of the concatenation. -/
theorem blockPosition_unique_revInv₂ {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hinj : ∀ b : Bool,
      Function.Injective (fun n : ℕ => (if b then h₁ else h₀) ^ n))
    (hnodup : ms.Nodup) {q q' : ℕ} {b : Bool} {x : G}
    (hq : (RelWord.revInv (relatorWord₂ p h₀ h₁ ms))[q]?
      = some (GGT.RelLetter.comp b x))
    (hq' : (RelWord.revInv (relatorWord₂ p h₀ h₁ ms))[q']?
      = some (GGT.RelLetter.comp b x)) :
    q = q' := by
  rw [revInv_relatorWord₂] at hq hq'
  exact getElem?_append_index_eq_left
    (nodup_revInv (nodup_blockWord hinj false ms hnodup))
    (notMem_revInv_map_base_of_comp p b x) hq hq'

/-- **Two rotations of the mirrored relator carrying the same block letter at
the same offset are equal.**  This closes the case of step (c) in which both
members of the symmetrized closure are rotations of the formal inverse: it makes
them the same word, which the corrected separation excludes by `w' ≠ w`. -/
theorem rotate_eq_of_block_at_offset_revInv₂ {p : List G} {h₀ h₁ : G}
    {ms : List ℕ}
    (hinj : ∀ b : Bool,
      Function.Injective (fun n : ℕ => (if b then h₁ else h₀) ^ n))
    (hnodup : ms.Nodup) {c c' d : ℕ} {b : Bool} {x : G}
    (hd : d < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length)
    (he : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d]?
      = some (GGT.RelLetter.comp b x))
    (he' : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c')[d]?
      = some (GGT.RelLetter.comp b x)) :
    (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c
      = (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c' :=
  rotate_eq_of_position_unique
    (fun _ _ hu hu' => blockPosition_unique_revInv₂ hinj hnodup hu hu') hd he he'

end MirrorRelator

end HullSC
end GroupApproximation
