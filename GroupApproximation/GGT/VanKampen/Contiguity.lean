import GroupApproximation.GGT.VanKampen.DiscDiagram
import GroupApproximation.GGT.HullSCPublishedSmallCancellation
import Mathlib.Tactic.Group

/-!
# Contiguity subdiagrams

This file formalizes the local part of Osin, Lemma 4.4 (`O52`).  A
contiguity region is a disc diagram with no relator cells.  Its exterior word
is split into a source arc, a short right side, the inverse of a target arc,
and a short left side.  The sides record both the literal length bound used by
the shared finite certificate and the relative word-norm bound used by Osin's
piece definition.  The empty-relator boundary theorem then gives the usual
connector equation between the two arc labels.

A cell-to-cell contiguity subdiagram also remembers the positions of the two
cells in the ordered relator-cell list.  The left side transports the base of
the first cell across the intervening cell values to the base of the second.
Diagram reducedness rules out equality of the two whole relators under this
transport, so the exposed source arc is a published `epsilon`-piece.  Hull's
published small-cancellation premise then proves
`|q| < mu |boundary Pi|`, and division by the positive cell length gives
contiguity degree less than `mu`.

The boundary version uses the same relator-free region and exposes the exact
outer subword.  It is the certificate consumed by the exterior-cell theorem
in the relative Greendlinger module.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC
open GroupApproximation.WordMetric

universe u w v

/-- A relator-free four-sided region between two labelled arcs. -/
structure ContiguityRegion
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ) where
  diagram : DiscDiagram.{u, w, v}
    (∅ : Set (List (GGT.RelLetter G Lambda)))
  no_relator_cells : diagram.relatorCells = []
  firstArc : List (GGT.RelLetter G Lambda)
  rightSide : List (GGT.RelLetter G Lambda)
  secondArc : List (GGT.RelLetter G Lambda)
  leftSide : List (GGT.RelLetter G Lambda)
  boundary_decomposition : diagram.boundaryWord =
    firstArc ++ rightSide ++ RelWord.revInv secondArc ++ leftSide
  leftSide_admissible : RelWord.IsAdmissible D leftSide
  rightSide_admissible : RelWord.IsAdmissible D rightSide
  leftSide_length_le : leftSide.length ≤ eps
  rightSide_length_le : rightSide.length ≤ eps
  leftSide_short : wordNorm D.alphabet.carrier
    (GGT.RelLetter.listVal leftSide) ≤ eps
  rightSide_short : wordNorm D.alphabet.carrier
    (GGT.RelLetter.listVal rightSide) ≤ eps

namespace ContiguityRegion

/-- The group element on the left side. -/
def leftConnector
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    (Gamma : ContiguityRegion.{u, w, v} D eps) : G :=
  GGT.RelLetter.listVal Gamma.leftSide

/-- The group element on the right side. -/
def rightConnector
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    (Gamma : ContiguityRegion.{u, w, v} D eps) : G :=
  GGT.RelLetter.listVal Gamma.rightSide

/-- The four-sided `G`-region gives the standard arc-label equation. -/
theorem arcs_value
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    (Gamma : ContiguityRegion.{u, w, v} D eps) :
    GGT.RelLetter.listVal Gamma.secondArc =
      Gamma.leftConnector * GGT.RelLetter.listVal Gamma.firstArc *
        Gamma.rightConnector := by
  have hboundary : Gamma.diagram.boundaryValue = 1 :=
    Gamma.diagram.boundaryValue_eq_one_of_no_rCells Gamma.no_relator_cells
  have hval :
      GGT.RelLetter.listVal Gamma.firstArc *
          GGT.RelLetter.listVal Gamma.rightSide *
          (GGT.RelLetter.listVal Gamma.secondArc)⁻¹ *
          GGT.RelLetter.listVal Gamma.leftSide = 1 := by
    rw [DiscDiagram.boundaryValue, Gamma.boundary_decomposition,
      RelWord.listVal_append, RelWord.listVal_append, RelWord.listVal_append,
      RelWord.listVal_revInv] at hboundary
    simpa only [mul_assoc] using hboundary
  have hcyclic :
      GGT.RelLetter.listVal Gamma.leftSide *
          GGT.RelLetter.listVal Gamma.firstArc *
          GGT.RelLetter.listVal Gamma.rightSide *
          (GGT.RelLetter.listVal Gamma.secondArc)⁻¹ = 1 := by
    calc
      GGT.RelLetter.listVal Gamma.leftSide *
            GGT.RelLetter.listVal Gamma.firstArc *
            GGT.RelLetter.listVal Gamma.rightSide *
            (GGT.RelLetter.listVal Gamma.secondArc)⁻¹ =
          GGT.RelLetter.listVal Gamma.leftSide *
            (GGT.RelLetter.listVal Gamma.firstArc *
              GGT.RelLetter.listVal Gamma.rightSide *
              (GGT.RelLetter.listVal Gamma.secondArc)⁻¹ *
              GGT.RelLetter.listVal Gamma.leftSide) *
            (GGT.RelLetter.listVal Gamma.leftSide)⁻¹ := by group
      _ = 1 := by rw [hval]; group
  calc
    GGT.RelLetter.listVal Gamma.secondArc =
        1 * GGT.RelLetter.listVal Gamma.secondArc := by rw [one_mul]
    _ = (GGT.RelLetter.listVal Gamma.leftSide *
          GGT.RelLetter.listVal Gamma.firstArc *
          GGT.RelLetter.listVal Gamma.rightSide *
          (GGT.RelLetter.listVal Gamma.secondArc)⁻¹) *
        GGT.RelLetter.listVal Gamma.secondArc := by rw [hcyclic]
    _ = Gamma.leftConnector * GGT.RelLetter.listVal Gamma.firstArc *
        Gamma.rightConnector := by
      rw [leftConnector, rightConnector]
      group

/-- The left connector has relative norm at most `eps`. -/
theorem leftConnector_short
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    (Gamma : ContiguityRegion.{u, w, v} D eps) :
    wordNorm D.alphabet.carrier Gamma.leftConnector ≤ eps :=
  Gamma.leftSide_short

/-- The right connector has relative norm at most `eps`. -/
theorem rightConnector_short
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    (Gamma : ContiguityRegion.{u, w, v} D eps) :
    wordNorm D.alphabet.carrier Gamma.rightConnector ≤ eps :=
  Gamma.rightSide_short

end ContiguityRegion

/-- An `epsilon`-contiguity subdiagram between two ordered relator cells.  The
target boundary is read oppositely, so its exposed prefix lies in
`revInv target.word`. -/
structure CellContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    (pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W))
    (source target : RelatorCell Delta.toCombMap Delta.outerFace W) where
  split : Delta.relatorCells =
    pre ++ source :: (between ++ target :: suf)
  region : ContiguityRegion.{u, w, v} D eps
  sourceRemainder : List (GGT.RelLetter G Lambda)
  source_decomposition : source.word = region.firstArc ++ sourceRemainder
  targetRemainder : List (GGT.RelLetter G Lambda)
  target_decomposition : RelWord.revInv target.word =
    region.secondArc ++ targetRemainder
  source_forward : source.reversed = false
  target_forward : target.reversed = false
  leftConnector_transport : region.leftConnector =
    (source.conjugator⁻¹ *
      (between.map RelatorCell.value).prod * target.conjugator)⁻¹

namespace CellContiguity

/-- Reducedness excludes equality of the two complete cell words under the
connector transport. -/
theorem whole_relators_ne
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hred : Delta.Reduced)
    (Gamma : CellContiguity.{u, w, v} (D := D) (eps := eps)
      pre between suf source target) :
    GGT.RelLetter.listVal (RelWord.revInv target.word) ≠
      Gamma.region.leftConnector * GGT.RelLetter.listVal source.word *
        Gamma.region.leftConnector⁻¹ := by
  rw [RelWord.listVal_revInv, Gamma.leftConnector_transport]
  intro hwhole
  have hnocancel := hred pre between suf source target Gamma.split
  apply hnocancel
  simp only [RelatorCell.value, Gamma.source_forward, Gamma.target_forward,
    Bool.false_eq_true, if_false]
  have htarget : GGT.RelLetter.listVal target.word =
      (Gamma.region.leftConnector * GGT.RelLetter.listVal source.word *
        Gamma.region.leftConnector⁻¹)⁻¹ := by
    have hinv := congrArg (fun g : G => g⁻¹) hwhole
    simpa only [inv_inv] using hinv
  rw [htarget, Gamma.leftConnector_transport]
  group

/-- Osin Lemma 4.4 (`O52`), local step: a cell-to-cell contiguity arc is a
published `epsilon`-piece. -/
theorem isPublishedPiece
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hred : Delta.Reduced)
    (Gamma : CellContiguity.{u, w, v} (D := D) (eps := eps)
      pre between suf source target) :
    RelWord.IsPublishedPiece D W eps Gamma.region.firstArc
      Gamma.region.secondArc source.word := by
  exact ⟨source.word_mem, ⟨Gamma.sourceRemainder,
    Gamma.source_decomposition⟩,
    RelWord.revInv target.word, hsc.inv_mem target.word target.word_mem,
    Gamma.targetRemainder, Gamma.target_decomposition,
    Gamma.region.leftConnector, Gamma.region.rightConnector,
    Gamma.region.leftConnector_short, Gamma.region.rightConnector_short,
    Gamma.region.arcs_value, Gamma.whole_relators_ne hred⟩

/-- The source contiguity arc is shorter than `mu` times the source-cell
boundary. -/
theorem sourceArc_lt_mu_mul
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hred : Delta.Reduced)
    (Gamma : CellContiguity.{u, w, v} (D := D) (eps := eps)
      pre between suf source target) :
    (Gamma.region.firstArc.length : ℝ) <
      mu * (source.word.length : ℝ) := by
  have hpublished := Gamma.isPublishedPiece hsc.toIsSmallCancellation hred
  have hbound := hsc.publishedPiecesSmall Gamma.region.firstArc
    Gamma.region.secondArc source.word hpublished
  exact lt_of_le_of_lt (le_max_left _ _) hbound

/-- Contiguity degree measured on the source cell. -/
noncomputable def degree
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (Gamma : CellContiguity.{u, w, v} (D := D) (eps := eps)
      pre between suf source target) : ℝ :=
  (Gamma.region.firstArc.length : ℝ) / source.word.length

/-- Osin Lemma 4.4 (`O52`): an interior contiguity degree is less than
`mu`. -/
theorem degree_lt_mu
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hrho : 0 < rho)
    (hred : Delta.Reduced)
    (Gamma : CellContiguity.{u, w, v} (D := D) (eps := eps)
      pre between suf source target) :
    Gamma.degree < mu := by
  have hlenNat : 0 < source.word.length :=
    lt_of_lt_of_le hrho (hsc.long source.word source.word_mem)
  have hlen : (0 : ℝ) < (source.word.length : ℝ) := by
    exact_mod_cast hlenNat
  rw [degree, div_lt_iff₀ hlen]
  exact Gamma.sourceArc_lt_mu_mul hsc hred

end CellContiguity

/-- An `epsilon`-contiguity subdiagram from a relator cell to a subword of the
outer boundary. -/
structure BoundaryContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    (source : RelatorCell Delta.toCombMap Delta.outerFace W) where
  source_mem : source ∈ Delta.relatorCells
  region : ContiguityRegion.{u, w, v} D eps
  sourceRemainder : List (GGT.RelLetter G Lambda)
  source_decomposition : source.word = region.secondArc ++ sourceRemainder
  boundaryBefore : List (GGT.RelLetter G Lambda)
  boundaryAfter : List (GGT.RelLetter G Lambda)
  boundary_decomposition : Delta.boundaryWord =
    boundaryBefore ++ region.firstArc ++ boundaryAfter

namespace BoundaryContiguity

/-- Exterior contiguity degree measured on the relator cell. -/
noncomputable def degree
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {source : RelatorCell Delta.toCombMap Delta.outerFace W}
    (Gamma : BoundaryContiguity.{u, w, v} (D := D) (eps := eps) source) : ℝ :=
  (Gamma.region.secondArc.length : ℝ) / source.word.length

/-- The exterior arc has no more letters than its source relator. -/
theorem sourceArc_length_le
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {source : RelatorCell Delta.toCombMap Delta.outerFace W}
    (Gamma : BoundaryContiguity.{u, w, v} (D := D) (eps := eps) source) :
    Gamma.region.secondArc.length ≤ source.word.length := by
  rw [Gamma.source_decomposition]
  simp only [List.length_append]
  omega

end BoundaryContiguity

end VanKampen
end GGT
end GroupApproximation
