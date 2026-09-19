import GroupApproximation.GGT.DGOLemma421Components
import GroupApproximation.Meta.AxiomGuard

/-!
# Quantitative positions of peripheral occurrences

Condition (W1) puts the first peripheral letter within one edge of the
initial vertex and successive letters within two edges of each other. Thus
rank `r` lies between positions `r` and `2r + 1`.
-/

namespace GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} {Lambda : Type w}

/-- The first peripheral position is no later than any peripheral letter. -/
theorem peripheralPos_zero_le_of_mem
    {word : List (RelLetter G Lambda)} {z : ℕ} (hz : z ∈ peripheralPositions word) :
    peripheralPos word 0 ≤ z := by
  have hcount : 0 < (peripheralPositions word).card := Finset.card_pos.mpr ⟨z, hz⟩
  let E := (peripheralPositions word).orderIsoOfFin rfl
  have hle := E.monotone (show (⟨0, hcount⟩ : Fin (peripheralPositions word).card) ≤
      E.symm ⟨z, hz⟩ by exact Nat.zero_le _)
  rw [E.apply_symm_apply] at hle
  unfold peripheralPos
  rw [dif_pos hcount]
  exact hle

/-- A W1 word with a peripheral letter has one in its first two positions. -/
theorem peripheralPos_zero_le_one
    {word : List (RelLetter G Lambda)} (hW1 : WWord.IsWOne word)
    (hcount : 0 < (peripheralPositions word).card) : peripheralPos word 0 ≤ 1 := by
  by_contra hnot
  have hpos := (List.getElem?_eq_some_iff.mp
    (peripheralOccurrence word ⟨0, hcount⟩).read).1
  change peripheralPos word 0 < word.length at hpos
  have hzero : 0 < word.length := by omega
  have hone : 1 < word.length := by omega
  have hbase : ∀ i : ℕ, i ≤ 1 → ∃ g : G, word[i]? = some (RelLetter.base g) := by
    intro i hi
    have hiword : i < word.length := by omega
    cases hread : word[i]'hiword with
    | base g => exact ⟨g, by simpa [List.getElem?_eq_getElem hiword] using hread⟩
    | comp nu g =>
      have hmem : i ∈ peripheralPositions word := mem_peripheralPositions_iff.mpr
        ⟨nu, g, by simpa [List.getElem?_eq_getElem hiword] using hread⟩
      have := peripheralPos_zero_le_of_mem hmem
      omega
  obtain ⟨g, hg⟩ := hbase 0 (by omega)
  obtain ⟨h, hh⟩ := hbase 1 le_rfl
  exact hW1 0 g h hg hh

/-- An ordered peripheral position is at least its rank and, in a W1 word,
at most twice its rank plus one. -/
theorem peripheralPos_bounds
    {word : List (RelLetter G Lambda)} (hW1 : WWord.IsWOne word)
    {r : ℕ} (hr : r < (peripheralPositions word).card) :
    r ≤ peripheralPos word r ∧ peripheralPos word r ≤ 2 * r + 1 := by
  induction r with
  | zero => exact ⟨Nat.zero_le _, by simpa using peripheralPos_zero_le_one hW1 hr⟩
  | succ r ih =>
    have hr' : r < (peripheralPositions word).card := by omega
    have hb := ih hr'
    have hlt := peripheralPos_lt hr (Nat.lt_succ_self r)
    have hle := peripheralPos_succ_le_add_two hW1 hr
    constructor <;> omega

/-- The same bounds in the canonical-occurrence interface. -/
theorem peripheralOccurrence_pos_bounds
    {word : List (RelLetter G Lambda)} (hW1 : WWord.IsWOne word)
    (r : Fin (peripheralPositions word).card) :
    r.val ≤ (peripheralOccurrence word r).pos ∧
      (peripheralOccurrence word r).pos ≤ 2 * r.val + 1 :=
  peripheralPos_bounds hW1 r.isLt

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.peripheralPos_zero_le_of_mem
#audit_axioms GroupApproximation.GGT.OsinComponents.peripheralPos_zero_le_one
#audit_axioms GroupApproximation.GGT.OsinComponents.peripheralPos_bounds
#audit_axioms GroupApproximation.GGT.OsinComponents.peripheralOccurrence_pos_bounds
