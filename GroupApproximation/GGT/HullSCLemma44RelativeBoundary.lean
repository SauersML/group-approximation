import GroupApproximation.GGT.HullSCLemma44RelativeDehn

/-!
# Reduced diagrams for a prescribed relative boundary word

The relative-area induction in Osin's Lemma 5.1 starts with a particular word
in the relative alphabet, not merely with its group value.  If that value is a
nonidentity element of the relator normal closure, this file constructs the
common `RelativeReducedDiagram` while retaining the prescribed boundary word.

The construction is algebraic.  Choose the least number of signed conjugates
of relator values whose product is the boundary value, flatten that product,
and orient every signed factor using inversion closure of the symmetrized
family.  Minimality gives the no-cancelling-pair condition.  The argument is
the prescribed-boundary version of `Lemma44RelatorDiagramBoundary.exists_reduced`
and `Lemma44ReducedRelatorDiagram.exists_oriented`.

Combining the diagram with a Greendlinger certificate and the cut theorem from
`HullSCLemma44RelativeDehn` gives a strictly shorter word with the same
quotient value.  This is the exact well-founded step used in equations
(18)--(21) of Osin's proof.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

/-! ## Least relative area at a fixed boundary -/

/-- A nonidentity element of the relator normal closure has positive least
relator area. -/
theorem exists_positive_least_relatorArea
    {G : Type u} [Group G] {Lambda : Type w}
    (W : Set (List (GGT.RelLetter G Lambda))) {boundary : G}
    (hboundary : boundary ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hne : boundary ≠ 1) :
    ∃ area : ℕ,
      0 < area ∧
      RelatorDefectBudget.IsRelatorProduct
        (GGT.RelLetter.listVal '' W) area boundary ∧
      ∀ {m : ℕ},
        RelatorDefectBudget.IsRelatorProduct
          (GGT.RelLetter.listVal '' W) m boundary → area ≤ m := by
  have hex : ∃ area, RelatorDefectBudget.IsRelatorProduct
      (GGT.RelLetter.listVal '' W) area boundary :=
    RelatorDefectBudget.exists_isRelatorProduct hboundary
  let area := Nat.find hex
  have harea : RelatorDefectBudget.IsRelatorProduct
      (GGT.RelLetter.listVal '' W) area boundary := Nat.find_spec hex
  have hpositive : 0 < area := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hareaZero : RelatorDefectBudget.IsRelatorProduct
        (GGT.RelLetter.listVal '' W) 0 boundary := by
      simpa only [hzero] using harea
    exact hne hareaZero.eq_one_of_index_zero
  exact ⟨area, hpositive, harea, fun h ⇒ Nat.find_min' hex h⟩

/-- The least-area normal-closure product, flattened and oriented factor by
factor, gives a reduced diagram with the supplied boundary spelling. -/
theorem exists_relativeReducedDiagram_of_boundaryWord
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (boundaryWord : List G) (boundary : G)
    (hword : IsWord D.alphabet.carrier boundaryWord boundary)
    (hne : boundary ≠ 1)
    (hboundary : boundary ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W)) :
    ∃ Z : RelativeReducedDiagram D W boundaryWord.length,
      Z.boundaryWord = boundaryWord := by
  obtain ⟨area, hareaPos, harea, hminimal⟩ :=
    exists_positive_least_relatorArea W hboundary hne
  obtain ⟨factors, hfactorsLength, hfactorsProd, hfactorsSigned⟩ :=
    harea.exists_flatten
  obtain ⟨cells, hcellValues⟩ :=
    exists_orientedRelatorCells hsc.inv_mem factors hfactorsSigned
  have hcellsLength : cells.length = area := by
    calc
      cells.length = factors.length := by
        have hlength := congrArg List.length hcellValues
        simpa only [List.length_map] using hlength
      _ = area := hfactorsLength
  have hcellsProd :
      (cells.map Lemma44OrientedRelatorCell.value).prod = boundary := by
    rw [hcellValues, hfactorsProd]
  refine ⟨{
    boundaryWord := boundaryWord
    boundary := boundary
    boundary_ne_one := hne
    boundaryWord_isWord := hword
    boundary_length_le := by omega
    area := area
    area_pos := hareaPos
    cells := cells
    cells_length := hcellsLength
    cell_values_prod := hcellsProd
    no_cancelling_pair := ?_ }, rfl⟩
  intro pre between suf C₁ C₂ hsplit
  apply RelatorDefectBudget.no_cancelling_pair_of_minimal
    hfactorsLength hfactorsProd hfactorsSigned hminimal
    (pre.map Lemma44OrientedRelatorCell.value)
    (between.map Lemma44OrientedRelatorCell.value)
    (suf.map Lemma44OrientedRelatorCell.value) C₁.value C₂.value
  rw [← hcellValues, hsplit]
  simp only [List.map_append, List.map_cons]

/-! ## From a kernel boundary to a strict cut -/

/-- A quotient-kernel equation turns a quotient-null source value into the
normal-closure membership used by the least-area construction. -/
theorem mem_normalClosure_of_map_eq_one
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    {boundary : G} (hmap : q boundary = 1) :
    boundary ∈ Subgroup.normalClosure (GGT.RelLetter.listVal '' W) := by
  rw [← hker]
  exact MonoidHom.mem_ker.mpr hmap

/-- Certificate availability for every reduced diagram shortens any specified
nontrivial quotient-null boundary word. -/
theorem exists_relativeDehnCut_of_kernelBoundary
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
      Nonempty (RelativeDiagramCertificate D W eps mu Z))
    (boundaryWord : List G) (boundary : G)
    (hword : IsWord D.alphabet.carrier boundaryWord boundary)
    (hne : boundary ≠ 1) (hmap : q boundary = 1) :
    Nonempty (RelativeDehnCut D W eps q boundaryWord) := by
  have hnormal : boundary ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W) :=
    mem_normalClosure_of_map_eq_one q hker hmap
  obtain ⟨Z, hZboundary⟩ := exists_relativeReducedDiagram_of_boundaryWord
    D W hsc.toIsSmallCancellation boundaryWord boundary hword hne hnormal
  obtain ⟨K⟩ := hcert boundaryWord.length Z
  have hcut := exists_relativeDehnCut_of_kernel D hsc hmu hrho K q hker
  rw [K.boundaryWord_eq, hZboundary] at hcut
  exact hcut

/-- Version whose boundary value is written as the word product. -/
theorem exists_relativeDehnCut_of_kernelWord
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
      Nonempty (RelativeDiagramCertificate D W eps mu Z))
    (boundaryWord : List G)
    (hword : IsWord D.alphabet.carrier boundaryWord boundaryWord.prod)
    (hne : boundaryWord.prod ≠ 1) (hmap : q boundaryWord.prod = 1) :
    Nonempty (RelativeDehnCut D W eps q boundaryWord) :=
  exists_relativeDehnCut_of_kernelBoundary D hsc hmu hrho q hker hcert
    boundaryWord boundaryWord.prod hword hne hmap

/-! ## Degenerate checks -/

/-- Existence of a strict cut forces the old boundary word to be nonempty. -/
theorem boundaryWord_length_pos_of_relativeDehnCut
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {eps : ℕ}
    {q : G →* Q} {boundaryWord : List G}
    (C : RelativeDehnCut D W eps q boundaryWord) : 0 < boundaryWord.length := by
  have hnonneg : 0 ≤ C.contiguity.shortenedBoundaryWord.length := Nat.zero_le _
  omega

/-- A one-point source has no nontrivial boundary to which the construction
could be applied. -/
theorem no_nontrivial_boundaryWord_trivialSource
    (boundaryWord : List PUnit) : ¬ boundaryWord.prod ≠ 1 := by
  intro hne
  exact hne (Subsingleton.elim _ _)

/-- The empty family has no nonidentity element in its normal closure. -/
theorem not_mem_empty_relator_normalClosure_of_ne_one
    {G : Type u} [Group G] {Lambda : Type w} {boundary : G}
    (hne : boundary ≠ 1) :
    boundary ∉ Subgroup.normalClosure
      (GGT.RelLetter.listVal ''
        (∅ : Set (List (GGT.RelLetter G Lambda)))) := by
  simpa only [Set.image_empty, Subgroup.normalClosure_empty,
    Subgroup.mem_bot] using hne

end HullSC
end GroupApproximation
