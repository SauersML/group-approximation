import GroupApproximation.GGT.HullSCRelatorSeparation2MirrorRun

/-!
# From an offset in a member of the closure to a position in the run

Steps (b) and (c) are stated at positions of the run: `blockPosition_unique₂` and
`HullSC.not_mirrored_block_match` read `blockWord` and its formal inverse.  Step
(a), on the other hand, will deliver its matched blocks at a common *offset* in
two members of the symmetrized closure, which are rotations.  This module is the
translation between the two, and it is needed under any form step (a) takes.

Three things happen in the translation, and only the third needs a hypothesis.

* A rotation read at an offset is the word read at the offset shifted modulo the
  length (`getElem?_of_rotate`).
* A position of the relator carrying a block letter is past the base part, so it
  is a position of the run (`blockIndex_of_relatorWord₂`); in the mirrored word
  the run comes first, so it is a position below `|ms|`
  (`blockIndex_of_revInv_relatorWord₂`).
* **Consecutive offsets are consecutive positions**, and this is where `p` has to
  be nonempty.  Reading two consecutive offsets can wrap around the end of the
  word, and then the two positions are `|R| - 1` and `0` rather than `q` and
  `q + 1`.  A nonempty base part rules that out on both sides: in the relator
  position `0` is a base letter, and in the mirrored relator position `|R| - 1`
  is.  The design supplies `0 < |p|` freely -- `p` spells `t⁻¹` and
  `HullSC.exists_long_base_spelling` makes it as long as wanted.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## Two arithmetic facts -/

/-- **Reading a rotation at an offset is reading the word at the shifted
position.** -/
theorem getElem?_of_rotate {α : Type v} {l : List α} {c d : ℕ}
    (hd : d < l.length) {x : α} (h : (l.rotate c)[d]? = some x) :
    l[(c + d) % l.length]? = some x := by
  have hl : 0 < l.length := Nat.lt_of_le_of_lt (Nat.zero_le d) hd
  rwa [getElem?_rotate_at hd, getElem?_rotate_head hl] at h

/-- **The step from one offset to the next, modulo the length**: either the
position advances by one, or it wraps to the start. -/
theorem mod_succ_cases (c d n : ℕ) (hn : 1 < n) :
    (c + (d + 1)) % n = (c + d) % n + 1 ∨
      ((c + d) % n + 1 = n ∧ (c + (d + 1)) % n = 0) := by
  have hadd : c + (d + 1) = c + d + 1 := by omega
  rw [hadd]
  have h1 : (c + d + 1) % n = ((c + d) % n + 1 % n) % n := Nat.add_mod (c + d) 1 n
  rw [Nat.mod_eq_of_lt hn] at h1
  have hlt : (c + d) % n < n := Nat.mod_lt _ (by omega)
  rcases Nat.lt_or_ge ((c + d) % n + 1) n with hcase | hcase
  · exact Or.inl (by rw [h1, Nat.mod_eq_of_lt hcase])
  · have he : (c + d) % n + 1 = n := by omega
    exact Or.inr ⟨he, by rw [h1, he, Nat.mod_self]⟩

/-! ## A block letter of the relator is a letter of the run -/

section Locate

variable {G : Type u} [Group G]

/-- **A position of the relator carrying a block letter is a position of the
run.**  The first `|p|` letters are base letters. -/
theorem blockIndex_of_relatorWord₂ {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    {q : ℕ} {b : Bool} {x : G}
    (hq : (relatorWord₂ p h₀ h₁ ms)[q]? = some (GGT.RelLetter.comp b x)) :
    ∃ i : ℕ, q = p.length + i ∧ i < ms.length ∧
      (blockWord h₀ h₁ false ms)[i]? = some (GGT.RelLetter.comp b x) := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hq
  rw [length_relatorWord₂] at hlt
  rcases Nat.lt_or_ge q p.length with hbase | hge
  · exfalso
    have h1 : (relatorWord₂ p h₀ h₁ ms)[q]?
        = (p.map GGT.RelLetter.base)[q]? := by
      show (p.map GGT.RelLetter.base ++ blockWord h₀ h₁ false ms)[q]? = _
      exact List.getElem?_append_left (by rwa [List.length_map])
    rw [h1] at hq
    exact notMem_map_base_of_comp p b x (List.mem_of_getElem? (i := q) hq)
  · refine ⟨q - p.length, by omega, by omega, ?_⟩
    have h3 := relatorWord₂_getElem?_block p h₀ h₁ ms (q - p.length)
    rw [show p.length + (q - p.length) = q from by omega] at h3
    rw [← h3]
    exact hq

/-- **A position of the mirrored relator carrying a block letter is a position
of the mirrored run.**  Inversion reverses the concatenation, so the run is what
comes first and the base part is what follows. -/
theorem blockIndex_of_revInv_relatorWord₂ {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    {t : ℕ} {b : Bool} {x : G}
    (ht : (RelWord.revInv (relatorWord₂ p h₀ h₁ ms))[t]?
      = some (GGT.RelLetter.comp b x)) :
    t < ms.length ∧
      (RelWord.revInv (blockWord h₀ h₁ false ms))[t]?
        = some (GGT.RelLetter.comp b x) := by
  rw [revInv_relatorWord₂] at ht
  have hlenb : (RelWord.revInv (blockWord h₀ h₁ false ms)).length = ms.length := by
    rw [RelWord.length_revInv, length_blockWord]
  rcases Nat.lt_or_ge t (RelWord.revInv (blockWord h₀ h₁ false ms)).length with
    hlt | hge
  · rw [List.getElem?_append_left hlt] at ht
    exact ⟨by omega, ht⟩
  · exfalso
    rw [List.getElem?_append_right hge] at ht
    exact notMem_revInv_map_base_of_comp p b x
      (List.mem_of_getElem?
        (i := t - (RelWord.revInv (blockWord h₀ h₁ false ms)).length) ht)

end Locate

/-! ## Consecutive offsets are consecutive positions -/

section Consecutive

variable {G : Type u} [Group G]

/-- **Two block letters at consecutive offsets of a rotation of the relator sit
at consecutive positions of the run.**  A wrap-around would put the second at
position `0`, which is a base letter. -/
theorem blockIndex_succ_of_rotate {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hp : 0 < p.length) {c d : ℕ}
    (hd : d + 1 < (relatorWord₂ p h₀ h₁ ms).length) {b b' : Bool} {x x' : G}
    (h : ((relatorWord₂ p h₀ h₁ ms).rotate c)[d]?
      = some (GGT.RelLetter.comp b x))
    (h' : ((relatorWord₂ p h₀ h₁ ms).rotate c)[d + 1]?
      = some (GGT.RelLetter.comp b' x')) :
    ∃ i : ℕ, i + 1 < ms.length ∧
      (blockWord h₀ h₁ false ms)[i]? = some (GGT.RelLetter.comp b x) ∧
      (blockWord h₀ h₁ false ms)[i + 1]? = some (GGT.RelLetter.comp b' x') := by
  have hlen : (relatorWord₂ p h₀ h₁ ms).length = p.length + ms.length :=
    length_relatorWord₂ p h₀ h₁ ms
  have hq := getElem?_of_rotate (by omega) h
  have hq' := getElem?_of_rotate hd h'
  obtain ⟨i, hqi, hi, hbi⟩ := blockIndex_of_relatorWord₂ hq
  obtain ⟨i', hq'i, hi', hbi'⟩ := blockIndex_of_relatorWord₂ hq'
  rcases mod_succ_cases c d (relatorWord₂ p h₀ h₁ ms).length (by omega) with
    hcase | ⟨-, hzero⟩
  · have hstep : p.length + i' = p.length + i + 1 := by
      rw [← hq'i, hcase, hqi]
    have hii : i' = i + 1 := by omega
    refine ⟨i, by omega, hbi, ?_⟩
    rw [← hii]
    exact hbi'
  · exfalso
    have hz : (0 : ℕ) = p.length + i' := hzero.symm.trans hq'i
    omega

/-- **The same for the mirrored relator.**  There the wrap-around would put the
first at the last position, which is a base letter. -/
theorem blockIndex_succ_of_rotate_revInv {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hp : 0 < p.length) {c d : ℕ}
    (hd : d + 1 < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length)
    {b b' : Bool} {x x' : G}
    (h : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d]?
      = some (GGT.RelLetter.comp b x))
    (h' : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d + 1]?
      = some (GGT.RelLetter.comp b' x')) :
    ∃ t : ℕ, t + 1 < ms.length ∧
      (RelWord.revInv (blockWord h₀ h₁ false ms))[t]?
        = some (GGT.RelLetter.comp b x) ∧
      (RelWord.revInv (blockWord h₀ h₁ false ms))[t + 1]?
        = some (GGT.RelLetter.comp b' x') := by
  have hlen : (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length
      = p.length + ms.length := by
    rw [RelWord.length_revInv, length_relatorWord₂]
  have hq := getElem?_of_rotate (by omega) h
  have hq' := getElem?_of_rotate hd h'
  obtain ⟨hi, hbi⟩ := blockIndex_of_revInv_relatorWord₂ hq
  rcases mod_succ_cases c d (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length
    (by omega) with hcase | ⟨hwrap, -⟩
  · rw [hcase] at hq'
    obtain ⟨hi', hbi'⟩ := blockIndex_of_revInv_relatorWord₂ hq'
    exact ⟨_, hi', hbi, hbi'⟩
  · exfalso
    omega

end Consecutive

end HullSC
end GroupApproximation
