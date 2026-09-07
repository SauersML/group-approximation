import GroupApproximation.GGT.VanKampen.DiscLabelNormalization

/-!
# A symmetric label alphabet with the original word metric

Adjoining inverse base labels changes admissible spellings but not the union
of the generators: that union was already symmetric. This auxiliary alphabet
is used only to normalize diagram labels. No transport of relative balls or
of the deep-relator clause of the small-cancellation condition is asserted.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

theorem symmetricLabelCarrier_eq (D : RelGenSet G Lambda) :
    {x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base} ∪ (⋃ i, (D.fam i : Set G)) =
      D.alphabet.carrier := by
  apply Set.Subset.antisymm
  · rintro x ((hx | hx) | hx)
    · exact Or.inl hx
    · have h : x⁻¹⁻¹ ∈ D.alphabet.carrier :=
        D.symmetricGenerating.inv_mem x⁻¹ (Or.inl hx)
      simpa only [inv_inv] using h
    · exact Or.inr hx
  · rintro x (hx | hx)
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx

def symmetricLabelAlphabet (D : RelGenSet G Lambda) : RelGenSet G Lambda where
  base := {x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}
  fam := D.fam
  symmetricGenerating := by
    rw [symmetricLabelCarrier_eq]
    exact D.symmetricGenerating

namespace symmetricLabelAlphabet

theorem symmetric (D : RelGenSet G Lambda) :
    ∀ x ∈ (symmetricLabelAlphabet D).base, x⁻¹ ∈ (symmetricLabelAlphabet D).base := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inr (by simpa only [inv_inv] using hx)
  · exact Or.inl hx

theorem carrier_eq (D : RelGenSet G Lambda) :
    (symmetricLabelAlphabet D).alphabet.carrier = D.alphabet.carrier :=
  symmetricLabelCarrier_eq D

theorem wordNorm_eq (D : RelGenSet G Lambda) (g : G) :
    WordMetric.wordNorm (symmetricLabelAlphabet D).alphabet.carrier g =
      WordMetric.wordNorm D.alphabet.carrier g := by
  rw [carrier_eq]

theorem isLetter (D : RelGenSet G Lambda) {a : RelLetter G Lambda} (ha : D.IsLetter a) :
    (symmetricLabelAlphabet D).IsLetter a := by
  cases a with
  | base x => exact Or.inl ha
  | comp i x => exact ha

theorem admissible (D : RelGenSet G Lambda) {word : List (RelLetter G Lambda)}
    (hword : RelWord.IsAdmissible D word) :
    RelWord.IsAdmissible (symmetricLabelAlphabet D) word :=
  fun a ha => isLetter D (hword a ha)

/-- Normalize arbitrary internal labels while retaining the literal original
exterior and ordered relator data. The original base need not be symmetric. -/
theorem exists_normalization (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (hboundary : RelWord.IsAdmissible D Delta.boundaryWord)
    (hcells : ∀ C ∈ Delta.relatorCells, RelWord.IsAdmissible D C.word) :
    Nonempty (DiscLabelNormalization.Output (symmetricLabelAlphabet D) Delta) :=
  DiscLabelNormalization.exists_output (symmetricLabelAlphabet D) (symmetric D) Delta
    (admissible D hboundary) (fun C hC => admissible D (hcells C hC))

end symmetricLabelAlphabet
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.symmetricLabelAlphabet.carrier_eq
#audit_axioms GroupApproximation.GGT.VanKampen.symmetricLabelAlphabet.wordNorm_eq
#audit_axioms GroupApproximation.GGT.VanKampen.symmetricLabelAlphabet.exists_normalization
