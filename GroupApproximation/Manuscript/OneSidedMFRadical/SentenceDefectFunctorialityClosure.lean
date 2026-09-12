import GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation

/-!
# Sentence-level closure of the defect-functoriality proof

This file names the two proof steps in census rows 194--195.  The target is
literally the range group `f(G)`, represented by `f.range`, and the conclusion
keeps the individual printed generator rather than mentioning only the final
subgroup inclusion.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

section

variable {G Q : Type*} [Group G] [Group Q]

/-- Centralizing `L` is preserved by a homomorphism.  This ambient-target
lemma is the elementwise calculation used by the range-group statement. -/
theorem map_commutesWithSubgroup
    (f : G →* Q) (L : Subgroup G) {c : G}
    (hc : ∀ delta ∈ L, Commute c delta) :
    ∀ eta ∈ L.map f, Commute (f c) eta := by
  intro eta heta
  rcases heta with ⟨delta, hdelta, rfl⟩
  exact (hc delta hdelta).map f

/-- **Sentence-census row 194.**  If `c ∈ C_G(L)`, then its image belongs
to `C_{f(G)}(f(L))`.  The range restriction makes the printed ambient group
`f(G)` literal in the theorem type. -/
theorem manuscriptMapCentralizerToRangeCentralizer
    (f : G →* Q) (L : Subgroup G) {c : G}
    (hc : ∀ delta ∈ L, Commute c delta) :
    ∀ eta ∈ L.map f.rangeRestrict,
      Commute (f.rangeRestrict c) eta :=
  map_commutesWithSubgroup f.rangeRestrict L hc

/-- An individual defining generator of the printed defect maps to an
individual defining generator for the mapped subgroup.  This is stronger in
exposure, but not in content, than immediately passing to normal closures. -/
theorem map_printedDefectGenerator_mem
    (f : G →* Q) (L : Subgroup G) {u c ell : G}
    (hu : u ∈ compressionSet L)
    (hc : ∀ delta ∈ L, Commute c delta) (hell : ell ∈ L) :
    f ⁅u * c * u⁻¹, ell⁆ ∈ printedDefect (L.map f) := by
  rw [map_commutatorElement, map_mul, map_mul, map_inv]
  exact printedDefect_generator_mem (L.map f)
    (map_mem_printedCompressionSet f L hu)
    (map_commutesWithSubgroup f L hc)
    ⟨ell, hell, rfl⟩

/-- **Sentence-census row 195, with row 193's compressor transport and row
194's centralizer transport visible.**  Every defining generator of `D`
lands in a defining-generator subgroup of `D_{f(G)}(f(L))`, with all three
transported inputs retained in the conclusion. -/
theorem manuscriptMapPrintedDefectGeneratorToRange
    (f : G →* Q) (L : Subgroup G) {u c ell : G}
    (hu : u ∈ compressionSet L)
    (hc : ∀ delta ∈ L, Commute c delta) (hell : ell ∈ L) :
    f.rangeRestrict u ∈ compressionSet (L.map f.rangeRestrict) ∧
      (∀ eta ∈ L.map f.rangeRestrict,
        Commute (f.rangeRestrict c) eta) ∧
      f.rangeRestrict ⁅u * c * u⁻¹, ell⁆ ∈
        printedDefect (L.map f.rangeRestrict) := by
  exact ⟨map_mem_printedCompressionSet f.rangeRestrict L hu,
    manuscriptMapCentralizerToRangeCentralizer f L hc,
    map_printedDefectGenerator_mem f.rangeRestrict L hu hc hell⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
