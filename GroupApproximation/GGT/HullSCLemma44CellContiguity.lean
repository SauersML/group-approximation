import GroupApproximation.GGT.HullSCLemma44OrientedCells

/-!
# Interior contiguity arcs in Hull's Lemma 4.4

An interior ε-contiguity subdiagram exposes oppositely oriented prefixes of
two relator cells and two short side arcs.  Its left side also transports the
stem of the first cell across the intervening cells to the stem of the second.
Least-area reducedness then proves Osin Lemma 4.3's whole-relator exclusion;
consequently the exposed run is a published ε-piece rather than carrying that
fact as a field.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u w

/-- Explicit algebraic labels of an interior ε-contiguity subdiagram between
two cells in their boundary order.  The second boundary is read oppositely,
which is why its exposed prefix belongs to `revInv C₂.relator`. -/
structure Lemma44CellContiguity
    {G : Type u} [Group G] {Λ : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Λ))} {R eps : ℕ}
    (E : GGT.RelGenSet G Λ) (Z : Lemma44OrientedRelatorDiagram A W R)
    (pre between suf : List (Lemma44OrientedRelatorCell W))
    (C₁ C₂ : Lemma44OrientedRelatorCell W)
    (hsplit : Z.cells = pre ++ C₁ :: (between ++ C₂ :: suf)) where
  firstArc : List (GGT.RelLetter G Λ)
  firstRemainder : List (GGT.RelLetter G Λ)
  first_decomposition : C₁.relator = firstArc ++ firstRemainder
  secondArc : List (GGT.RelLetter G Λ)
  secondRemainder : List (GGT.RelLetter G Λ)
  second_decomposition : RelWord.revInv C₂.relator = secondArc ++ secondRemainder
  leftConnector : G
  rightConnector : G
  leftConnector_short : wordNorm E.alphabet.carrier leftConnector ≤ eps
  rightConnector_short : wordNorm E.alphabet.carrier rightConnector ≤ eps
  arcs_value : GGT.RelLetter.listVal secondArc =
    leftConnector * GGT.RelLetter.listVal firstArc * rightConnector
  leftConnector_stem : leftConnector =
    (C₁.conjugator⁻¹ *
      (between.map Lemma44OrientedRelatorCell.value).prod *
      C₂.conjugator)⁻¹

namespace Lemma44CellContiguity

/-- Osin Lemma 4.3: an interior contiguity run is a published piece.  The
nonconjugacy clause is a theorem of least-area reducedness, not part of the
contiguity datum. -/
theorem isPublishedPiece
    {G : Type u} [Group G] {Λ : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Λ))} {R eps : ℕ}
    {E : GGT.RelGenSet G Λ} {Z : Lemma44OrientedRelatorDiagram A W R}
    {pre between suf : List (Lemma44OrientedRelatorCell W)}
    {C₁ C₂ : Lemma44OrientedRelatorCell W}
    {hsplit : Z.cells = pre ++ C₁ :: (between ++ C₂ :: suf)}
    (hinv : ∀ v ∈ W, RelWord.revInv v ∈ W)
    (C : Lemma44CellContiguity (eps := eps) E Z pre between suf C₁ C₂ hsplit) :
    RelWord.IsPublishedPiece E W eps C.firstArc C.secondArc C₁.relator := by
  have hwhole : GGT.RelLetter.listVal (RelWord.revInv C₂.relator) ≠
      C.leftConnector * GGT.RelLetter.listVal C₁.relator *
        C.leftConnector⁻¹ := by
    rw [RelWord.listVal_revInv, C.leftConnector_stem]
    intro hcancel
    apply Z.relators_ne_inverseConjugate pre between suf C₁ C₂ hsplit
    have hinvEq := congrArg Inv.inv hcancel
    rw [inv_inv] at hinvEq
    rw [hinvEq]
    group
  exact ⟨C₁.relator_mem, ⟨C.firstRemainder, C.first_decomposition⟩,
    RelWord.revInv C₂.relator, hinv C₂.relator C₂.relator_mem,
    C.secondRemainder, C.second_decomposition,
    C.leftConnector, C.rightConnector,
    C.leftConnector_short, C.rightConnector_short, C.arcs_value, hwhole⟩

end Lemma44CellContiguity

end HullSC
end GroupApproximation
