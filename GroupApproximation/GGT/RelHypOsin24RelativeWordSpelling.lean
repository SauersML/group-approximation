import GroupApproximation.GGT.RelHypOsin24BoundedWordPattern

/-!
# Lifting relative alphabet words to labelled relative words

The metric alphabet `D.alphabet.carrier` forgets whether an occurrence came
from the finite base or from a peripheral subgroup.  Osin's relative words
retain that label.  This file proves the elementary lift between the two
presentations: every word over the alphabet has a word over `RelLetter` with
the same product, length, and admissibility.  A peripheral occurrence uses any
index witnessing its membership in the peripheral union.

This is the exact conversion needed before the finite-pattern pigeonhole in
`RelHypOsin24BoundedWordPattern`.  It is not the geometric step in Osin's
Memoirs Lemmas `cyc1`, `qc1`, and `qc-hyp`: those lemmas turn repeated labelled
patterns into a fixed peripheral double-coset slice, and remain represented by
`RelativeBoundedPowerExtractionStatement`.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.WordMetric

universe u v

theorem exists_relLetter_of_mem_alphabet {G : Type u} [Group G]
    {I : Type v} (D : RelGenSet G I) {x : G}
    (hx : x ∈ D.alphabet.carrier) :
    ∃ a : RelLetter G I, D.IsLetter a ∧ a.val = x := by
  change x ∈ D.base ∪ ⋃ i : I, (D.fam i : Set G) at hx
  rcases hx with hxbase | hxperiph
  · exact ⟨RelLetter.base x, hxbase, rfl⟩
  · rw [Set.mem_iUnion] at hxperiph
    obtain ⟨i, hxi⟩ := hxperiph
    exact ⟨RelLetter.comp i x, hxi, rfl⟩

/-- Every word in the unlabelled relative alphabet lifts to an admissible
labelled word with the same product and the same length. -/
theorem exists_relLetterWord_of_alphabet_word {G : Type u} [Group G]
    {I : Type v} (D : RelGenSet G I) {l : List G}
    (hl : ∀ x ∈ l, x ∈ D.alphabet.carrier) :
    ∃ w : List (RelLetter G I),
      (∀ a ∈ w, D.IsLetter a) ∧ w.length = l.length ∧
        RelLetter.listVal w = l.prod := by
  induction l with
  | nil =>
      exact ⟨[], by simp, by simp, by simp [RelLetter.listVal]⟩
  | cons x l ih =>
      have hx : x ∈ D.alphabet.carrier := hl x (by simp)
      have hl' : ∀ y ∈ l, y ∈ D.alphabet.carrier := by
        intro y hy
        exact hl y (List.mem_cons_of_mem x hy)
      obtain ⟨a, ha, haval⟩ := exists_relLetter_of_mem_alphabet D hx
      obtain ⟨w, hw, hwlen, hwval⟩ := ih hl'
      refine ⟨a :: w, ?_, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact ha
        · exact hw b hb
      · simp [hwlen]
      · calc
          RelLetter.listVal (a :: w) = a.val * RelLetter.listVal w := by rfl
          _ = x * l.prod := by rw [haval, hwval]
          _ = (x :: l).prod := by rfl

/-- **Relative-word spelling from a metric word norm bound.**  Every element
whose `D.alphabet` word norm is at most `N` has an admissible labelled spelling
of length at most `N`.  The proof is only the choice of an index for each
peripheral letter. -/
def RelativeWordSpellingStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v)
    (D : RelGenSet G I), ∀ (x : G) (N : ℕ),
      wordNorm D.alphabet.carrier x ≤ N →
        ∃ w : List (RelLetter G I),
          (∀ a ∈ w, D.IsLetter a) ∧ w.length ≤ N ∧
            RelLetter.listVal w = x

theorem relativeWordSpelling_proved : RelativeWordSpellingStatement.{u, v} := by
  intro G instG I D x N hN
  letI : Group G := instG
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq
    D.alphabet.symmetricGenerating x
  obtain ⟨w, hw, hwlen, hwval⟩ :=
    exists_relLetterWord_of_alphabet_word D (fun y hy => hl.letters y hy)
  refine ⟨w, hw, ?_, ?_⟩
  · rw [hwlen, hlen]
    exact hN
  · rw [hwval, hl.prod_eq]

/-- In the one-point group, the empty spelling witnesses every bound. -/
theorem relativeWordSpelling_trivialModel
    {I : Type v} (D : RelGenSet PUnit I) (x : PUnit) (N : ℕ) :
    wordNorm D.alphabet.carrier x ≤ N →
      ∃ w : List (RelLetter PUnit I),
        (∀ a ∈ w, D.IsLetter a) ∧ w.length ≤ N ∧
          RelLetter.listVal w = x := by
  intro hN
  obtain ⟨w, hw, hlen, hval⟩ :=
    relativeWordSpelling_proved PUnit inferInstance I D x N hN
  exact ⟨w, hw, hlen, hval⟩

end RelHyp
end GGT
end GroupApproximation
