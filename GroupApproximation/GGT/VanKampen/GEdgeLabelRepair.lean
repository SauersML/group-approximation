import GroupApproximation.GGT.VanKampen.GEdgeWordCellMap
import GroupApproximation.GGT.VanKampen.DartExpansionVertices

/-!
# Repairing one non-generator edge strictly decreases the remaining defects

The raw word subdivision does not require all other labels to be legal.
Every newly illegal dart instead comes from an unchanged old dart. Replacing
an illegal edge by a word legal in both orientations therefore strictly
decreases the finite number of illegal darts, regardless of word length.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

open scoped Classical

noncomputable def illegalDarts (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W) :
    Finset Delta.toCombMap.Dart := Finset.univ.filter fun d => ¬ D.IsLetter (Delta.label d)

namespace GEdgeWordSubdivision.RawOutput

variable {Delta : DiscDiagram.{u, w, v} W} {a : Delta.toCombMap.Dart}
  {word : List (RelLetter G Lambda)} (R : RawOutput Delta a word)

theorem other_darts (d : Delta.toCombMap.Dart)
    (ha : d ≠ a) (hb : d ≠ Delta.toCombMap.alpha a) :
    R.expansion.darts d = [R.expansion.toDartExpansion.first d] := by
  have hlen := congrArg List.length (R.other_word d ha hb)
  simp only [List.length_map, List.length_singleton] at hlen
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  have hfirst : R.expansion.toDartExpansion.first d = x := by
    simp only [DartExpansion.first, hx, List.head_cons]
  exact hx.trans (congrArg List.singleton hfirst.symm)

theorem illegalDarts_subset (D : RelGenSet G Lambda)
    (hword : RelWord.IsAdmissible D word)
    (hinv : ∀ l ∈ word, D.IsLetter (RelWord.inv l)) :
    illegalDarts D R.diagram ⊆
      ((illegalDarts D Delta).erase a).image R.expansion.toDartExpansion.first := by
  intro x hx
  have hxBad := (Finset.mem_filter.mp hx).2
  obtain ⟨d, hd⟩ := R.expansion.exists_old_dart x
  have hletter : R.diagram.label x ∈ (R.expansion.darts d).map R.diagram.label :=
    List.mem_map.mpr ⟨x, hd, rfl⟩
  by_cases ha : d = a
  · subst d
    rw [R.word_eq] at hletter
    exact (hxBad (hword _ hletter)).elim
  · by_cases hb : d = Delta.toCombMap.alpha a
    · subst d
      rw [R.expansion.word_alpha, R.word_eq] at hletter
      obtain ⟨l, hl, hleq⟩ := List.mem_map.mp (List.mem_reverse.mp hletter)
      exact (hxBad (hleq ▸ hinv l hl)).elim
    · rw [R.other_word d ha hb] at hletter
      have hl := List.mem_singleton.mp hletter
      have hdBad : d ∈ illegalDarts D Delta := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, fun hadm => hxBad (hl.symm ▸ hadm)⟩
      rw [R.other_darts d ha hb] at hd
      exact Finset.mem_image.mpr ⟨d, Finset.mem_erase.mpr ⟨ha, hdBad⟩,
        (List.mem_singleton.mp hd).symm⟩

/-- A potentially long replacement word still removes at least the chosen
illegal dart and introduces no new illegal dart. -/
theorem illegalDarts_card_lt (D : RelGenSet G Lambda)
    (hword : RelWord.IsAdmissible D word)
    (hinv : ∀ l ∈ word, D.IsLetter (RelWord.inv l))
    (ha : ¬ D.IsLetter (Delta.label a)) :
    (illegalDarts D R.diagram).card < (illegalDarts D Delta).card := by
  have haMem : a ∈ illegalDarts D Delta := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  calc
    (illegalDarts D R.diagram).card ≤
        (((illegalDarts D Delta).erase a).image R.expansion.toDartExpansion.first).card :=
      Finset.card_le_card (R.illegalDarts_subset D hword hinv)
    _ ≤ ((illegalDarts D Delta).erase a).card := Finset.card_image_le
    _ < (illegalDarts D Delta).card := Finset.card_lt_card (Finset.erase_ssubset haMem)

end GEdgeWordSubdivision.RawOutput
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision.RawOutput.illegalDarts_subset
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision.RawOutput.illegalDarts_card_lt
