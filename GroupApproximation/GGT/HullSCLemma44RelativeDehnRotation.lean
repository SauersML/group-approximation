import GroupApproximation.GGT.HullSCLemma44RelativeDehn

/-!
# Dehn cuts across the chosen boundary basepoint

A cyclic boundary rotation conjugates its product.  A local cut therefore
preserves the quotient value when the original boundary is quotient-null,
even if its contiguity arc crosses the basepoint.  These lemmas retain the
original boundary word and do not assume that a certificate's rotation is zero.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

namespace RelativeBoundaryContiguity

/-- The zero-rotation premise quantified over every contiguity is impossible:
even an empty boundary can be read with rotation one. -/
theorem not_all_rotation_zero
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ) :
    ¬ (∀ {boundaryWord : List G} {relator : List (GGT.RelLetter G Lambda)}
      (C : RelativeBoundaryContiguity D eps boundaryWord relator), C.rotation = 0) := by
  intro h
  let C : RelativeBoundaryContiguity D eps [] [] := {
    exterior := []
    remainder := []
    relator_decomposition := rfl
    rotation := 1
    boundaryBefore := []
    boundaryArc := []
    boundaryAfter := []
    boundary_decomposition := rfl
    leftSide := []
    rightSide := []
    leftSide_admissible := by simp [RelWord.IsAdmissible]
    rightSide_admissible := by simp [RelWord.IsAdmissible]
    leftSide_short := Nat.zero_le _
    rightSide_short := Nat.zero_le _
    exterior_value := by simp [GGT.RelLetter.listVal] }
  exact Nat.one_ne_zero (h C)

/-- Read the same contiguity at the boundary basepoint it specifies. -/
def atRotatedBoundary
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    RelativeBoundaryContiguity D eps (boundaryWord.rotate C.rotation) relator :=
  { C with
    rotation := 0
    boundary_decomposition := by simpa only [List.rotate_zero] using C.boundary_decomposition }

/-- The cut preserves the quotient product at the rotated basepoint. -/
theorem map_shortenedBoundaryWord_prod_eq_rotated
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (q : G →* Q) (hrelator : q (GGT.RelLetter.listVal relator) = 1) :
    q C.shortenedBoundaryWord.prod = q (boundaryWord.rotate C.rotation).prod :=
  C.atRotatedBoundary.map_shortenedBoundaryWord_prod_eq q hrelator rfl

/-- A quotient-null boundary stays quotient-null after a cyclic cut. -/
theorem map_shortenedBoundaryWord_prod_eq_of_map_eq_one
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (q : G →* Q) (hrelator : q (GGT.RelLetter.listVal relator) = 1)
    (hboundary : q boundaryWord.prod = 1) :
    q C.shortenedBoundaryWord.prod = q boundaryWord.prod := by
  rw [C.map_shortenedBoundaryWord_prod_eq_rotated q hrelator, hboundary]
  have hmap : (boundaryWord.map q).prod = 1 := by
    simpa only [map_list_prod] using hboundary
  have hrot := List.prod_rotate_eq_one_of_prod_eq_one hmap C.rotation
  simpa only [map_list_prod, List.map_rotate] using hrot

/-- Removing one cell gives the product identity at the rotated basepoint. -/
theorem rotatedBoundaryWord_prod_eq_conjugate_relator_mul_shortened
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    (boundaryWord.rotate C.rotation).prod =
      (C.boundaryBefore.prod * (GGT.RelLetter.listVal C.leftSide)⁻¹) *
        GGT.RelLetter.listVal relator *
        (C.boundaryBefore.prod * (GGT.RelLetter.listVal C.leftSide)⁻¹)⁻¹ *
        C.shortenedBoundaryWord.prod :=
  C.atRotatedBoundary.boundaryWord_prod_eq_conjugate_relator_mul_shortened rfl

end RelativeBoundaryContiguity

/-- Rotation changes a word product by conjugation by its moved prefix. -/
theorem word_prod_eq_conj_rotate_prod
    {G : Type u} [Group G] (word : List G) (rotation : ℕ) :
    word.prod = (word.take (rotation % word.length)).prod *
      (word.rotate rotation).prod * (word.take (rotation % word.length)).prod⁻¹ := by
  by_cases hnil : word = []
  · subst word
    simp
  have hpos : 0 < word.length := List.length_pos_iff.mpr hnil
  have hle : rotation % word.length ≤ word.length := (Nat.mod_lt _ hpos).le
  rw [← List.rotate_mod, List.rotate_eq_drop_append_take hle, List.prod_append]
  have hsplit := congrArg List.prod (List.take_append_drop (rotation % word.length) word)
  rw [List.prod_append] at hsplit
  rw [← hsplit]
  group

/-- A kernel equation makes every reduced diagram's designated boundary
quotient-null, since that boundary is a product of conjugate relators. -/
theorem map_certificate_boundaryWord_prod_eq_one
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps : ℕ} {mu : ℝ} {Z : RelativeReducedDiagram D W R}
    (K : RelativeDiagramCertificate D W eps mu Z)
    (q : G →* Q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W)) :
    q K.boundaryWord.prod = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [hker, K.boundaryWord_eq, Z.boundaryWord_isWord.prod_eq, ← Z.cell_values_prod]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨C, _, rfl⟩ := List.mem_map.mp hx
  have hbase : GGT.RelLetter.listVal C.relator ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W) :=
    Subgroup.subset_normalClosure ⟨C.relator, C.relator_mem, rfl⟩
  exact Subgroup.normalClosure_normal.conj_mem _ hbase C.conjugator

/-- A certificate cuts a quotient-null word without restricting its rotation. -/
theorem exists_relativeDehnCut_of_certificate_of_map_eq_one
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ} {Z : RelativeReducedDiagram D W R}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (K : RelativeDiagramCertificate D W eps mu Z)
    (q : G →* Q)
    (hkill : ∀ relator ∈ W, q (GGT.RelLetter.listVal relator) = 1)
    (hboundary : q K.boundaryWord.prod = 1) :
    Nonempty (RelativeDehnCut D W eps q K.boundaryWord) := by
  obtain ⟨i, C, _, hshort⟩ :=
    replacementWord_length_lt_boundaryArc_of_certificate D hsc hmu hrho K
  have hword : IsWord D.alphabet.carrier K.boundaryWord K.boundaryWord.prod := by
    refine ⟨?_, rfl⟩
    intro x hx
    apply Z.boundaryWord_isWord.letters x
    rwa [← K.boundaryWord_eq]
  exact ⟨{
    relator := K.cellLabel i
    relator_mem := K.cellLabel_mem i
    contiguity := C
    shortenedWord_isWord := C.shortenedBoundaryWord_isWord hword
      (hsc.admissible _ (K.cellLabel_mem i))
    quotient_value := C.map_shortenedBoundaryWord_prod_eq_of_map_eq_one q
      (hkill _ (K.cellLabel_mem i)) hboundary
    replacement_length_lt := hshort }⟩

/-- The normal-closure kernel equation supplies both nullity premises. -/
theorem exists_relativeDehnCut_of_kernel_rotated
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ} {Z : RelativeReducedDiagram D W R}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (K : RelativeDiagramCertificate D W eps mu Z)
    (q : G →* Q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W)) :
    Nonempty (RelativeDehnCut D W eps q K.boundaryWord) := by
  apply exists_relativeDehnCut_of_certificate_of_map_eq_one D hsc hmu hrho K q
  · intro relator hrelator
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact Subgroup.subset_normalClosure ⟨relator, hrelator, rfl⟩
  · exact map_certificate_boundaryWord_prod_eq_one K q hker

/-- Killing the relators also kills every certificate boundary, which is a
product of conjugate relator values. -/
theorem map_certificate_boundaryWord_prod_eq_one_of_kills_relators
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps : ℕ} {mu : ℝ} {Z : RelativeReducedDiagram D W R}
    (K : RelativeDiagramCertificate D W eps mu Z) (q : G →* Q)
    (hkill : ∀ relator ∈ W, q (GGT.RelLetter.listVal relator) = 1) :
    q K.boundaryWord.prod = 1 := by
  rw [K.boundaryWord_eq, Z.boundaryWord_isWord.prod_eq, ← Z.cell_values_prod,
    map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨C, _, rfl⟩ := List.mem_map.mp hx
  change q (C.conjugator * GGT.RelLetter.listVal C.relator * C.conjugator⁻¹) = 1
  rw [map_mul, map_mul, map_inv, hkill C.relator C.relator_mem]
  group

/-- Every certificate supplies a strict Dehn cut when the quotient kills its
relators, with no restriction on the contiguity's rotation. -/
theorem exists_relativeDehnCut_of_certificate
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ} {Z : RelativeReducedDiagram D W R}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (K : RelativeDiagramCertificate D W eps mu Z) (q : G →* Q)
    (hkill : ∀ relator ∈ W, q (GGT.RelLetter.listVal relator) = 1) :
    Nonempty (RelativeDehnCut D W eps q K.boundaryWord) :=
  exists_relativeDehnCut_of_certificate_of_map_eq_one D hsc hmu hrho K q hkill
    (map_certificate_boundaryWord_prod_eq_one_of_kills_relators K q hkill)

/-- The kernel form of the rotation-independent certificate cut. -/
theorem exists_relativeDehnCut_of_kernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ} {Z : RelativeReducedDiagram D W R}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (K : RelativeDiagramCertificate D W eps mu Z) (q : G →* Q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W)) :
    Nonempty (RelativeDehnCut D W eps q K.boundaryWord) :=
  exists_relativeDehnCut_of_kernel_rotated D hsc hmu hrho K q hker

end HullSC
end GroupApproximation
