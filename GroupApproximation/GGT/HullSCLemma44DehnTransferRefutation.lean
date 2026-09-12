import GroupApproximation.GGT.HullSCLemma44AreaTransferRefutation
import GroupApproximation.Meta.AxiomGuard

/-!
# The relative Dehn transfer is false

`RelativeDehnTransferStatement` (`GGT/HullSCLemma44RelativeIsoperimetric.lean`)
asks for relative-isoperimetric control of a quotient from two hypotheses only:
finite peripheral-letter support of the relator family, and a one-relator Dehn
cut at every nonidentity quotient-null word.  No small-cancellation condition,
no relator-length bound and no certificate appears in it.

The grid quotient of `GGT/HullSCLemma44AreaTransferRefutation.lean` refutes it
as well.  There every quotient-null word on the free basis of `F₂` is itself a
relator, so every such word carries a cut: the whole word is the contiguity arc,
the relator is its own letterwise spelling, both connectors are empty, and the
replacement word is empty, hence strictly shorter than the arc.  The quotient is
`ℤ²` with the Manhattan metric, which fails every four-point bound.

So the route
`relativeIsoperimetricBridgeStatement_of_dehnTransfer` cannot be fed, and every
statement that implies `RelativeDehnTransferStatement` is false too.  In
particular the transfer over the cut-or-shortening disjunction, whose hypothesis
is weaker, is false, which is why no such proposition is stated anywhere as a
target for Osin's Lemma 5.1.  What Osin's induction does deliver is linear
relative area (`relativeLinearKernelArea_of_quasiGeodesicCertificates`,
`GGT/HullSCLemma51QuasiGeodesicTransfer.lean`); the passage from linear area to
geometry needs the relator-length bound of `BoundedRelativeLinearAreaTransferStatement`.
-/

namespace GroupApproximation.HullSC

open WordMetric Hyperbolic

namespace DehnTransferRefutation

open AreaTransferRefutation

/-- **The whole word as its own contiguity arc.**  The relator is the letterwise
spelling of the boundary word, the exterior is the whole relator, and both
connectors and the complementary arc are empty. -/
def wholeWordContiguity (boundaryWord : List (FreeGroup Bool)) :
    RelativeBoundaryContiguity source 0 boundaryWord
      (boundaryWord.map GGT.RelLetter.base) where
  exterior := boundaryWord.map GGT.RelLetter.base
  remainder := []
  relator_decomposition := (List.append_nil _).symm
  rotation := 0
  boundaryBefore := []
  boundaryArc := boundaryWord
  boundaryAfter := []
  boundary_decomposition := by simp
  leftSide := []
  rightSide := []
  leftSide_admissible := fun a ha => by simp at ha
  rightSide_admissible := fun a ha => by simp at ha
  leftSide_short := by simp
  rightSide_short := by simp
  exterior_value := by
    simp [GGT.RelLetter.listVal, List.map_map, Function.comp_def,
      GGT.RelLetter.val]

/-- The replacement word of the whole-word contiguity is empty. -/
theorem wholeWordContiguity_replacementWord (boundaryWord : List (FreeGroup Bool)) :
    (wholeWordContiguity boundaryWord).replacementWord = [] := by
  simp [RelativeBoundaryContiguity.replacementWord, wholeWordContiguity,
    RelWord.revInv]

/-- The shortened boundary word of the whole-word contiguity is empty. -/
theorem wholeWordContiguity_shortenedBoundaryWord
    (boundaryWord : List (FreeGroup Bool)) :
    (wholeWordContiguity boundaryWord).shortenedBoundaryWord = [] := by
  rw [RelativeBoundaryContiguity.shortenedBoundaryWord,
    wholeWordContiguity_replacementWord]
  simp [wholeWordContiguity]

/-- **Every nonidentity quotient-null basis word carries a Dehn cut** over the
family of all quotient-null basis words. -/
theorem exists_wholeWordCut (boundaryWord : List (FreeGroup Bool))
    (hword : IsWord source.alphabet.carrier boundaryWord boundaryWord.prod)
    (hne : boundaryWord.prod ≠ 1) (hmap : quotient boundaryWord.prod = 1) :
    Nonempty (RelativeDehnCut source kernelRelators 0 quotient boundaryWord) := by
  have hletters : ∀ x ∈ boundaryWord, x ∈ freeAlphabet Bool := by
    intro x hx
    simpa [source_alphabet] using hword.letters x hx
  have hnonempty : boundaryWord ≠ [] := by
    intro h
    apply hne
    simp [h]
  have hshort := wholeWordContiguity_shortenedBoundaryWord boundaryWord
  have hrepl := wholeWordContiguity_replacementWord boundaryWord
  refine ⟨{
    relator := boundaryWord.map GGT.RelLetter.base
    relator_mem := ⟨boundaryWord, hletters, hmap, rfl⟩
    contiguity := wholeWordContiguity boundaryWord
    shortenedWord_isWord := ?_
    quotient_value := ?_
    replacement_length_lt := ?_ }⟩
  · rw [hshort]
    exact ⟨fun x hx => by simp at hx, rfl⟩
  · rw [hshort, List.prod_nil, map_one, hmap]
  · rw [hrepl]
    change 0 < boundaryWord.length
    exact Nat.pos_of_ne_zero (by simpa using hnonempty)

end DehnTransferRefutation

/-- **`RelativeDehnTransferStatement` is false.**  At the grid quotient of `F₂`,
with every quotient-null basis word as a relator, the support hypothesis holds
because there are no peripheral letters, every nonidentity kernel word carries
the whole-word cut, and the image alphabet fails every four-point bound. -/
theorem not_relativeDehnTransferStatement :
    ¬ RelativeDehnTransferStatement.{0, 0, 0} := by
  intro h
  obtain ⟨C⟩ := h AreaTransferRefutation.source
    AreaTransferRefutation.source_embedded AreaTransferRefutation.kernelRelators 0
    AreaTransferRefutation.quotient AreaTransferRefutation.quotient_surjective
    AreaTransferRefutation.kernelRelators_support
    (fun boundaryWord hword hne hmap =>
      DehnTransferRefutation.exists_wholeWordCut boundaryWord hword hne hmap)
  have hfour := C.fourPoint
  rw [GGT.RelGenSet.alphabet_carrier_mapSurjective,
    AreaTransferRefutation.source_alphabet] at hfour
  exact AreaTransferRefutation.grid_not_fourPoint C.delta hfour

end GroupApproximation.HullSC

#audit_axioms GroupApproximation.HullSC.DehnTransferRefutation.exists_wholeWordCut
#audit_closed_axioms GroupApproximation.HullSC.not_relativeDehnTransferStatement
