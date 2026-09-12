import GroupApproximation.GGT.HullSCFilling

/-!
# Separating the quotient alphabet from suitability preservation

`FillingAlphabetData` contains two logically different outputs of Hull's
small-cancellation construction.  First, the quotient receives a Hull
generating set containing the image of the old alphabet.  Second, the image of
`N` and the images of all prescribed suitable subgroups remain suitable.

This file separates those outputs.  The first is `QuotientHullAlphabet`; after
it has been constructed, `SuitableImagesInQuotient` is the exact remaining
suitability premise.  For the torsion-free quotients produced by Hull's lifting
clause, that premise is equivalent to preservation of non-elementarity: the
finite-normalizer half of suitability is automatic.  The assembly back to
`FillingAlphabetData` is immediate and proved below.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- A Hull alphabet on the quotient containing the image of the source
alphabet, without any assertion yet about distinguished subgroups. -/
structure QuotientHullAlphabet {G : Type u} [Group G]
    (A : HullGeneratingSet G) {Q : Type u} [Group Q] (q : G →* Q) where
  hullSet : HullGeneratingSet Q
  alphabet_image : ∀ a ∈ A.alphabet.carrier,
    q a ∈ hullSet.alphabet.carrier

/-- **The exact remaining suitability premise once the quotient alphabet is
fixed.** -/
def SuitableImagesInQuotient {G : Type u} [Group G]
    {A : HullGeneratingSet G} (N : Subgroup G) {k : ℕ}
    (S : Fin k → Subgroup G) {Q : Type u} [Group Q] (q : G →* Q)
    (B : QuotientHullAlphabet A q) : Prop :=
  Suitable B.hullSet.alphabet (N.map q) ∧
    ∀ j : Fin k, Suitable B.hullSet.alphabet ((S j).map q)

/-- **Over a torsion-free quotient, only non-elementarity remains.**

Hull's second suitability clause asks the subgroup to normalize no nontrivial
finite subgroup.  Power torsion-freeness makes every finite subgroup of the
ambient quotient trivial, so the quotient-filling lane only has to preserve
two independent loxodromics in each distinguished image. -/
theorem suitableImagesInQuotient_of_torsionFree
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} {Q : Type u} [Group Q] {q : G →* Q}
    (B : QuotientHullAlphabet A q) (hQ : IsPowerTorsionFree Q)
    (hN : ActsNonElementarily (N.map q) (Cayley.base B.hullSet.alphabet))
    (hS : ∀ j : Fin k,
      ActsNonElementarily ((S j).map q) (Cayley.base B.hullSet.alphabet)) :
    SuitableImagesInQuotient N S q B := by
  refine ⟨⟨hN, ?_⟩, fun j => ⟨hS j, ?_⟩⟩
  · exact HullSuitable.normalizesNoNontrivialFinite_of_torsionFree hQ (N.map q)
  · exact HullSuitable.normalizesNoNontrivialFinite_of_torsionFree hQ ((S j).map q)

/-- **Exact quotient-suitability residue over a torsion-free quotient.** -/
theorem suitableImagesInQuotient_iff_actsNonElementarily
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} {Q : Type u} [Group Q] {q : G →* Q}
    (B : QuotientHullAlphabet A q) (hQ : IsPowerTorsionFree Q) :
    SuitableImagesInQuotient N S q B ↔
      ActsNonElementarily (N.map q) (Cayley.base B.hullSet.alphabet) ∧
        ∀ j : Fin k,
          ActsNonElementarily ((S j).map q) (Cayley.base B.hullSet.alphabet) := by
  constructor
  · intro h
    exact ⟨h.1.actsNonElementarily, fun j => (h.2 j).actsNonElementarily⟩
  · rintro ⟨hN, hS⟩
    exact suitableImagesInQuotient_of_torsionFree B hQ hN hS

/-- The separated alphabet and suitability outputs reassemble to the original
`FillingAlphabetData`. -/
def FillingAlphabetData.ofQuotientHullAlphabet
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} {Q : Type u} [Group Q] {q : G →* Q}
    (B : QuotientHullAlphabet A q) (hsuit : SuitableImagesInQuotient N S q B) :
    FillingAlphabetData A N S q where
  hullSet := B.hullSet
  alphabet_image := B.alphabet_image
  suitable_map := hsuit.1
  suitable_map_family := hsuit.2

/-- Conversely, existing filling data projects to the quotient alphabet. -/
def FillingAlphabetData.toQuotientHullAlphabet
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} {Q : Type u} [Group Q] {q : G →* Q}
    (F : FillingAlphabetData A N S q) : QuotientHullAlphabet A q where
  hullSet := F.hullSet
  alphabet_image := F.alphabet_image

/-- Existing filling data also projects to the exact suitability premise. -/
theorem FillingAlphabetData.suitableImagesInQuotient
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} {Q : Type u} [Group Q] {q : G →* Q}
    (F : FillingAlphabetData A N S q) :
    SuitableImagesInQuotient N S q F.toQuotientHullAlphabet :=
  ⟨F.suitable_map, F.suitable_map_family⟩

/-- Nonempty filling data is equivalent to a quotient Hull alphabet together
with suitability of all distinguished images. -/
theorem nonempty_fillingAlphabetData_iff
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} {Q : Type u} [Group Q] {q : G →* Q} :
    Nonempty (FillingAlphabetData A N S q) ↔
      ∃ B : QuotientHullAlphabet A q, SuitableImagesInQuotient N S q B := by
  constructor
  · rintro ⟨F⟩
    exact ⟨F.toQuotientHullAlphabet, F.suitableImagesInQuotient⟩
  · rintro ⟨B, hsuit⟩
    exact ⟨FillingAlphabetData.ofQuotientHullAlphabet B hsuit⟩

end HullSC
end GroupApproximation
