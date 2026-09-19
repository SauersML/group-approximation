import GroupApproximation.GGT.OsinTheorem54SepReversal
import GroupApproximation.GGT.VanKampen.NonemptyConnectorWord

/-!
# Reversible spellings without symmetrizing the relative base

The existing reversible-substitute theorem changes only relative-letter tags,
preserving the word's length and all path vertices. Here its output is carried
as actual data for diagram insertion, whose reversal uses `RelWord.inv`.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC OsinComponents
universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

structure ReversibleSpelling (D : RelGenSet G Lambda) (original : List (RelLetter G Lambda)) where
  word : List (RelLetter G Lambda)
  admissible : RelWord.IsAdmissible D word
  inverse_admissible : ∀ l ∈ word, D.IsLetter (RelWord.inv l)
  length_eq : word.length = original.length
  vertex_eq : ∀ (v : G) (i : ℕ), vertex v word i = vertex v original i

theorem exists_reversibleSpelling (D : RelGenSet G Lambda)
    (original : List (RelLetter G Lambda)) (hadm : RelWord.IsAdmissible D original) :
    Nonempty (ReversibleSpelling D original) := by
  obtain ⟨word, hlen, hadm', hinv, hvertices⟩ := exists_reversibleSubstitute D original hadm
  refine ⟨⟨word, hadm', ?_, hlen, hvertices⟩⟩
  intro l hl
  have h := hinv (invLetter l)
    (List.mem_reverse.mpr (List.mem_map.mpr ⟨l, hl, rfl⟩))
  exact h

namespace ReversibleSpelling

variable {D : RelGenSet G Lambda} {original : List (RelLetter G Lambda)}
  (S : ReversibleSpelling D original)

theorem value_eq : RelLetter.listVal S.word = RelLetter.listVal original := by
  have hs := vertex_length (1 : G) S.word
  have ho := vertex_length (1 : G) original
  have hv := S.vertex_eq (1 : G) original.length
  rw [S.length_eq] at hs
  rw [hs, ho] at hv
  simpa only [one_mul] using hv

theorem nonempty (hne : original ≠ []) : S.word ≠ [] := by
  intro h
  have hl := S.length_eq
  rw [h, List.length_nil] at hl
  exact hne (List.length_eq_zero_iff.mp hl.symm)

theorem revInv_admissible : RelWord.IsAdmissible D (RelWord.revInv S.word) := by
  intro l hl
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hl)
  exact S.inverse_admissible a ha

end ReversibleSpelling

/-- Every legal letter can be respelled so both edge orientations are legal,
with the same group value and no change to the relative generating set. -/
theorem exists_inverse_legal_letter (D : RelGenSet G Lambda)
    (a : RelLetter G Lambda) (ha : D.IsLetter a) :
    ∃ b : RelLetter G Lambda, D.IsLetter b ∧ D.IsLetter (RelWord.inv b) ∧ b.val = a.val :=
  exists_isLetter_invLetter_of_isLetter D ha

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.exists_reversibleSpelling
#audit_axioms GroupApproximation.GGT.VanKampen.ReversibleSpelling.value_eq
#audit_axioms GroupApproximation.GGT.VanKampen.exists_inverse_legal_letter
