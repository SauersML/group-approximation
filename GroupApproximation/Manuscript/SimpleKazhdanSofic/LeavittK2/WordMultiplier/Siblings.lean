import GroupApproximation.Leavitt.PrefixCode
import Mathlib.Data.Fintype.BigOperators
import GroupApproximation.Meta.AxiomGuard

/-!
# Sibling words and the complete sibling leaf set

Lane `sk-leavitt-08`, Khanh (arXiv:2609.08428v1), proof of Lemma 4.1 (`lem:word-multiplier`).

Khanh, tex l.352: "For a word $\eta=c_1\cdots c_h$, $h\geq1$, let
$s_\ell=c_1\cdots c_{\ell-1}c'_\ell$, where $c'_\ell$ is the other binary letter. The words
$\eta,s_1,\ldots,s_h$ form a complete leaf set."

## Route

* `flipBit c = c + 1` is the other binary letter; `sibling η ℓ = η.take ℓ ++ [flipBit η[ℓ]]`
  (0-indexed, so `sibling η ℓ` is Khanh's `s_{ℓ+1}`).
* Prefix-freeness: all these words branch off `η` at a letter where they disagree
  (`not_prefix_of_bit_ne`).
* Completeness by telescoping `cylinder_split`:
  `p_{η↾k} + ∑_{ℓ<k} p_{sibling η ℓ} = 1` for `k ≤ |η|`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open scoped BigOperators

/-- The other binary letter `c'`. -/
def flipBit (c : Fin 2) : Fin 2 := c + 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.flipBit

theorem flipBit_zero : flipBit 0 = 1 := by decide

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.flipBit_zero

theorem flipBit_one : flipBit 1 = 0 := by decide

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.flipBit_one

theorem flipBit_ne (c : Fin 2) : flipBit c ≠ c := by
  revert c
  decide

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.flipBit_ne

/-- Khanh's sibling word `s_{ℓ+1} = c_1 ⋯ c_ℓ c'_{ℓ+1}` (0-indexed position `ℓ`). -/
def sibling (η : List (Fin 2)) (ℓ : ℕ) : List (Fin 2) :=
  η.take ℓ ++ [flipBit ((η[ℓ]?).getD 0)]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.sibling

theorem sibling_eq (η : List (Fin 2)) {ℓ : ℕ} (hℓ : ℓ < η.length) :
    sibling η ℓ = η.take ℓ ++ [flipBit η[ℓ]] := by
  rw [sibling, List.getElem?_eq_getElem hℓ, Option.getD_some]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.sibling_eq

/-- Words that disagree right after a common prefix are prefix-incomparable. -/
theorem not_prefix_of_bit_ne (p u v : List (Fin 2)) {c d : Fin 2} (hcd : c ≠ d) :
    ¬ p ++ c :: u <+: p ++ d :: v := by
  rw [List.prefix_append_right_inj, List.cons_prefix_cons]
  exact fun h => hcd h.1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.not_prefix_of_bit_ne

theorem eq_take_append_getElem_cons (η : List (Fin 2)) {ℓ : ℕ} (hℓ : ℓ < η.length) :
    η = η.take ℓ ++ η[ℓ] :: η.drop (ℓ + 1) := by
  rw [← List.drop_eq_getElem_cons hℓ, List.take_append_drop]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.eq_take_append_getElem_cons

/-- A later sibling still passes through the letter `η[ℓ]` at position `ℓ`. -/
theorem sibling_eq_of_lt (η : List (Fin 2)) {ℓ ℓ' : ℕ} (hlt : ℓ < ℓ')
    (hℓ' : ℓ' < η.length) :
    ∃ v, sibling η ℓ' = η.take ℓ ++ η[ℓ]'(by omega) :: v := by
  have hℓ : ℓ < η.length := by omega
  have hpre : η.take (ℓ + 1) <+: η.take ℓ' := List.take_prefix_take_left (by omega)
  obtain ⟨r, hr⟩ := hpre
  refine ⟨r ++ [flipBit η[ℓ']], ?_⟩
  rw [sibling_eq η hℓ', ← hr, List.take_succ_eq_append_getElem hℓ]
  simp only [List.append_assoc, List.singleton_append]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.sibling_eq_of_lt

theorem sibling_not_prefix_eta (η : List (Fin 2)) {ℓ : ℕ} (hℓ : ℓ < η.length) :
    ¬ sibling η ℓ <+: η := by
  have key := not_prefix_of_bit_ne (η.take ℓ) [] (η.drop (ℓ + 1)) (flipBit_ne η[ℓ])
  rw [← eq_take_append_getElem_cons η hℓ] at key
  rwa [sibling_eq η hℓ]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.sibling_not_prefix_eta

theorem eta_not_prefix_sibling (η : List (Fin 2)) {ℓ : ℕ} (hℓ : ℓ < η.length) :
    ¬ η <+: sibling η ℓ := by
  have key :=
    not_prefix_of_bit_ne (η.take ℓ) (η.drop (ℓ + 1)) [] (flipBit_ne η[ℓ]).symm
  rw [← eq_take_append_getElem_cons η hℓ] at key
  rwa [sibling_eq η hℓ]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.eta_not_prefix_sibling

theorem sibling_incomparable (η : List (Fin 2)) {ℓ ℓ' : ℕ} (hne : ℓ ≠ ℓ')
    (hℓ : ℓ < η.length) (hℓ' : ℓ' < η.length) :
    ¬ sibling η ℓ <+: sibling η ℓ' := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨v, hv⟩ := sibling_eq_of_lt η hlt hℓ'
    rw [hv, sibling_eq η hℓ]
    exact not_prefix_of_bit_ne (η.take ℓ) [] v (flipBit_ne η[ℓ])
  · obtain ⟨v, hv⟩ := sibling_eq_of_lt η hlt hℓ
    rw [hv, sibling_eq η hℓ']
    exact not_prefix_of_bit_ne (η.take ℓ') v [] (flipBit_ne η[ℓ']).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.sibling_incomparable

/-- The leaf set `η, s_1, …, s_h`, indexed by `Option (Fin h)`. -/
def siblingWord (η : List (Fin 2)) : Option (Fin η.length) → List (Fin 2)
  | none => η
  | some ℓ => sibling η ℓ

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.siblingWord

/-- The sibling leaf set as a binary prefix code (tex l.352). -/
def siblingCode (η : List (Fin 2)) : BinaryPrefixCode (Option (Fin η.length)) where
  word := siblingWord η
  prefix_free := by
    intro i j hij
    rcases i with _ | ℓ <;> rcases j with _ | ℓ'
    · exact absurd rfl hij
    · exact eta_not_prefix_sibling η ℓ'.isLt
    · exact sibling_not_prefix_eta η ℓ.isLt
    · have hne : (ℓ : ℕ) ≠ (ℓ' : ℕ) := fun h => hij (congrArg some (Fin.ext h))
      exact sibling_incomparable η hne ℓ.isLt ℓ'.isLt

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.siblingCode

section Cylinders

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- Splitting a cylinder along a letter `c` and its flip. -/
theorem cylinder_split_bit (p : List (Fin 2)) (c : Fin 2) :
    L.cylinder p = L.cylinder (p ++ [c]) + L.cylinder (p ++ [flipBit c]) := by
  rcases (show ∀ d : Fin 2, d = 0 ∨ d = 1 by decide) c with rfl | rfl
  · rw [flipBit_zero]
    exact L.cylinder_split p
  · rw [flipBit_one, add_comm]
    exact L.cylinder_split p

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cylinder_split_bit

/-- Telescoping: `p_{η↾k} + ∑_{ℓ<k} p_{s_{ℓ+1}} = 1` for `k ≤ |η|`. -/
theorem cylinder_take_add_sum_sibling (η : List (Fin 2)) :
    ∀ k, k ≤ η.length →
      L.cylinder (η.take k) + ∑ ℓ ∈ Finset.range k, L.cylinder (sibling η ℓ) = 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [LeavittFamily.cylinder]
  | succ k ih =>
    intro hk
    have hk' : k < η.length := by omega
    have h := ih (by omega)
    rw [cylinder_split_bit L (η.take k) η[k]] at h
    rw [Finset.sum_range_succ, List.take_succ_eq_append_getElem hk', sibling_eq η hk', ← h]
    abel

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cylinder_take_add_sum_sibling

/-- **Sibling completeness** (tex l.352): `η, s_1, …, s_h` is a complete leaf set. -/
theorem sibling_complete (η : List (Fin 2)) : L.IsComplete (siblingCode η) := by
  have h := cylinder_take_add_sum_sibling L η η.length le_rfl
  rw [List.take_length, ← Fin.sum_univ_eq_sum_range] at h
  unfold LeavittFamily.IsComplete
  rw [Fintype.sum_option]
  exact h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.sibling_complete

end Cylinders

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
