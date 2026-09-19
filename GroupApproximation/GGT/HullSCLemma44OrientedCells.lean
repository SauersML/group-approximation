import GroupApproximation.GGT.HullSCLemma44ReducedDiagram

/-!
# Oriented relator cells for Hull's Lemma 4.4

The flat least-area certificate stores signed conjugates as group elements.
The planar contiguity argument needs actual oriented cells: a conjugator and a
word of the symmetrized relator family.  Inversion closure absorbs every
negative sign into `revInv`, so every factor has a positive oriented cell.

The last theorem transports the least-area no-cancelling-pair condition to
these cells, including cells separated by an arbitrary intervening block.
This is the exact reducedness input used by a noncrossing/contiguity matching.
-/

namespace GroupApproximation
namespace HullSC

universe u w

/-- An oriented relator cell and its conjugating stem. -/
structure Lemma44OrientedRelatorCell {G : Type u} [Group G] {Λ : Type w}
    (W : Set (List (GGT.RelLetter G Λ))) where
  conjugator : G
  relator : List (GGT.RelLetter G Λ)
  relator_mem : relator ∈ W

namespace Lemma44OrientedRelatorCell

/-- The group element contributed by an oriented cell. -/
def value {G : Type u} [Group G] {Λ : Type w}
    {W : Set (List (GGT.RelLetter G Λ))}
    (C : Lemma44OrientedRelatorCell W) : G :=
  C.conjugator * GGT.RelLetter.listVal C.relator * C.conjugator⁻¹

/-- Inversion closure orients a signed conjugate without changing its value. -/
theorem exists_of_signedConjugate
    {G : Type u} [Group G] {Λ : Type w}
    {W : Set (List (GGT.RelLetter G Λ))}
    (hinv : ∀ v ∈ W, RelWord.revInv v ∈ W) {x : G}
    (hx : RelatorDefectBudget.IsSignedConjugate
      (GGT.RelLetter.listVal '' W) x) :
    ∃ C : Lemma44OrientedRelatorCell W, C.value = x := by
  obtain ⟨c, _, ⟨v, hv, rfl⟩, hx | hx⟩ := hx
  · exact ⟨⟨c, v, hv⟩, hx.symm⟩
  · refine ⟨⟨c, RelWord.revInv v, hinv v hv⟩, ?_⟩
    rw [value, RelWord.listVal_revInv]
    exact hx.symm

end Lemma44OrientedRelatorCell

/-- Every flat signed-conjugate list can be oriented, factor for factor. -/
theorem exists_orientedRelatorCells
    {G : Type u} [Group G] {Λ : Type w}
    {W : Set (List (GGT.RelLetter G Λ))}
    (hinv : ∀ v ∈ W, RelWord.revInv v ∈ W) :
    ∀ factors : List G,
      (∀ x ∈ factors, RelatorDefectBudget.IsSignedConjugate
        (GGT.RelLetter.listVal '' W) x) →
      ∃ cells : List (Lemma44OrientedRelatorCell W),
        cells.map Lemma44OrientedRelatorCell.value = factors
  | [], _ => ⟨[], rfl⟩
  | x :: xs, hcells => by
      obtain ⟨C, hC⟩ := Lemma44OrientedRelatorCell.exists_of_signedConjugate
        hinv (hcells x (by simp))
      obtain ⟨tail, htail⟩ := exists_orientedRelatorCells hinv xs
        (fun y hy => hcells y (by simp [hy]))
      exact ⟨C :: tail, by simp [hC, htail]⟩

/-- A reduced least-area diagram with every relator factor oriented by a word
of the given symmetrized family. -/
structure Lemma44OrientedRelatorDiagram {G : Type u} [Group G]
    {Λ : Type w} (A : Manuscript.NonMF.TorsionFree.Alphabet G)
    (W : Set (List (GGT.RelLetter G Λ))) (R : ℕ)
    extends Lemma44ReducedRelatorDiagram A W R where
  cells : List (Lemma44OrientedRelatorCell W)
  cell_values : cells.map Lemma44OrientedRelatorCell.value = factors

/-- Inversion closure of the small-cancellation family constructs the oriented
cell list. -/
theorem Lemma44ReducedRelatorDiagram.exists_oriented
    {G : Type u} [Group G] {Λ : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Λ))} {R eps rho : ℕ} {mu : ℝ}
    (Z : Lemma44ReducedRelatorDiagram A W R)
    {E : GGT.RelGenSet G Λ} (hsc : RelWord.IsSmallCancellation E W eps mu rho) :
    Nonempty (Lemma44OrientedRelatorDiagram A W R) := by
  obtain ⟨cells, hcells⟩ :=
    exists_orientedRelatorCells hsc.inv_mem Z.factors Z.factors_signed
  exact ⟨{
    toLemma44ReducedRelatorDiagram := Z
    cells := cells
    cell_values := hcells
  }⟩

/-- The cell-level reducedness condition: two oriented cells cannot cancel
across the value of all cells between them. -/
theorem Lemma44OrientedRelatorDiagram.noCancellingCellPair
    {G : Type u} [Group G] {Λ : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Λ))} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram A W R)
    (pre between suf : List (Lemma44OrientedRelatorCell W))
    (C₁ C₂ : Lemma44OrientedRelatorCell W)
    (hsplit : Z.cells = pre ++ C₁ :: (between ++ C₂ :: suf)) :
    ((between.map Lemma44OrientedRelatorCell.value).prod)⁻¹ * C₁.value *
        (between.map Lemma44OrientedRelatorCell.value).prod * C₂.value ≠ 1 := by
  apply Z.no_cancelling_pair
    (pre.map Lemma44OrientedRelatorCell.value)
    (between.map Lemma44OrientedRelatorCell.value)
    (suf.map Lemma44OrientedRelatorCell.value) C₁.value C₂.value
  rw [← Z.cell_values, hsplit]
  simp only [List.map_append, List.map_cons]

/-- **Reducedness on the actual oriented cell boundaries.**  Let `B` be the
product of the cells strictly between `C₁` and `C₂`.  Transporting from the
stem of `C₁`, across `B`, to the stem of `C₂` gives

`d = C₁.conjugator⁻¹ * B * C₂.conjugator`.

The two relator boundaries cannot be inverse conjugates by `d`.  If they were,
then the two complete cells would cancel across the intervening subdiagram,
contradicting `noCancellingCellPair`.  This is the exact whole-cell exclusion
needed when a relative cancellation matching turns a maximal common boundary
run into a published piece; it mentions the relator words themselves rather
than only the flattened factor values. -/
theorem Lemma44OrientedRelatorDiagram.relators_ne_inverseConjugate
    {G : Type u} [Group G] {Λ : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Λ))} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram A W R)
    (pre between suf : List (Lemma44OrientedRelatorCell W))
    (C₁ C₂ : Lemma44OrientedRelatorCell W)
    (hsplit : Z.cells = pre ++ C₁ :: (between ++ C₂ :: suf)) :
    GGT.RelLetter.listVal C₂.relator ≠
      ((C₁.conjugator⁻¹ *
          (between.map Lemma44OrientedRelatorCell.value).prod *
          C₂.conjugator)⁻¹ *
        (GGT.RelLetter.listVal C₁.relator)⁻¹ *
        (C₁.conjugator⁻¹ *
          (between.map Lemma44OrientedRelatorCell.value).prod *
          C₂.conjugator)) := by
  intro hcancel
  apply Z.noCancellingCellPair pre between suf C₁ C₂ hsplit
  rw [Lemma44OrientedRelatorCell.value,
    Lemma44OrientedRelatorCell.value, hcancel]
  group

end HullSC
end GroupApproximation
