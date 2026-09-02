import GroupApproximation.GGT.KazhdanHypGirthEightVKInterface
import GroupApproximation.GGT.VanKampen.CactusRealization

/-!
# Clean cactus boundary producers

This module stays on the clean cactus closure.  In particular it does not
import the high-level Build file, whose reduction dependency currently goes
through sep2fix's repairing `Estimating.PieceBridge`.

The landed `VanKampen.cactusRealizationStatement` starts with an oriented
least-area algebraic diagram.  The source predicate below supplies precisely
that object with its exact boundary spelling.  A second adapter turns it into
the literal reduced disc diagram by the named cactus realization theorem.

The separate retyping availability theorem is not repeated here: its landed
type lives in `CombMapReduction.lean`, whose current import path includes
`PieceBridge`.  The exact residual is recorded in the clean Build module and
can be connected once that imported API is green.
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypGirthEightCactusProducer

open GroupApproximation.HullSC
open GroupApproximation.KazhdanHyp
open GroupApproximation.Manuscript.NonMF.TorsionFree

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

def freeLetter (u : TriangularHodgeLayer.SignedGenerator Generator) :
    FreeGroup Generator :=
  FoxBoundary.letterValue FreeGroup.of u

def relativeWord
    (w : List (TriangularHodgeLayer.SignedGenerator Generator)) :
    List (GGT.RelLetter (FreeGroup Generator) PEmpty) :=
  w.map (fun u => GGT.RelLetter.base (freeLetter u))

def PresentedWordIsTrivial
    (w : List (TriangularHodgeLayer.SignedGenerator Generator)) : Prop :=
  PresentedGroup.mk
      (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
      (PresentedGroupRelatorReplay.word w) = 1

/-! ## Oriented algebraic source -/

def OrientedCactusBoundaryProducer : Prop :=
  ∀ (w : List (TriangularHodgeLayer.SignedGenerator Generator)),
    PresentedWordIsTrivial (T := T) w →
    (w.map freeLetter).prod ≠ 1 →
    ∃ (A : Alphabet (FreeGroup Generator)) (R : ℕ)
      (Z : Lemma44OrientedRelatorDiagram.{0, 0} A
        (triangleRelatorWords T) R),
      Z.boundaryWord = w.map freeLetter

def OrientedCactusBoundarySource : Prop :=
  ∀ (w : List (TriangularHodgeLayer.SignedGenerator Generator)),
    PresentedWordIsTrivial (T := T) w →
    (w.map freeLetter).prod ≠ 1 →
    ∃ (A : Alphabet (FreeGroup Generator)) (R : ℕ)
      (Z : Lemma44OrientedRelatorDiagram.{0, 0} A
        (triangleRelatorWords T) R),
      Z.boundaryWord = w.map freeLetter

omit [Fintype Generator] [DecidableEq TriangleIndex] in
theorem orientedCactusBoundaryProducer_of_source
    (hsource : OrientedCactusBoundarySource (T := T)) :
    OrientedCactusBoundaryProducer (T := T) := by
  intro w hw hfree
  obtain ⟨A, R, Z, hboundary⟩ :=
    hsource w hw hfree
  exact ⟨A, R, Z, hboundary⟩

/-! ## Cactus realization and literal boundary spelling -/

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
theorem cactusRealization_of_oriented
    {A : Alphabet (FreeGroup Generator)} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram.{0, 0} A
      (triangleRelatorWords T) R) :
    Nonempty (VanKampen.CactusRealization Z) :=
  VanKampen.cactusRealizationStatement Z

def CactusDiscDiagramProducer : Prop :=
  ∀ (w : List (TriangularHodgeLayer.SignedGenerator Generator)),
    PresentedWordIsTrivial (T := T) w →
    (w.map freeLetter).prod ≠ 1 →
    ∃ Delta : VanKampen.DiscDiagram.{0, 0, 0}
        (triangleRelatorWords T),
      Delta.boundaryWord = relativeWord w ∧ Delta.Reduced

omit [Fintype Generator] [DecidableEq TriangleIndex] in
theorem cactusDiscDiagramProducer_of_oriented
    (hproducer : OrientedCactusBoundaryProducer (T := T)) :
    CactusDiscDiagramProducer (T := T) := by
  intro w hw hfree
  obtain ⟨A, R, Z, hboundary⟩ := hproducer w hw hfree
  obtain ⟨C⟩ := cactusRealization_of_oriented Z
  have hrelative : ∀ w : List (TriangularHodgeLayer.SignedGenerator Generator),
      (w.map freeLetter).map
          (GGT.RelLetter.base : FreeGroup Generator →
            GGT.RelLetter (FreeGroup Generator) PEmpty) = relativeWord w := by
    intro w
    induction w with
    | nil => rfl
    | cons u us ih =>
        simp only [List.map_cons]
        exact congrArg (List.cons (GGT.RelLetter.base (freeLetter u))) ih
  refine ⟨C.diagram, ?_, C.reduced⟩
  calc
    C.diagram.boundaryWord = Z.boundaryWord.map
        (GGT.RelLetter.base : FreeGroup Generator →
          GGT.RelLetter (FreeGroup Generator) PEmpty) := C.boundaryWord_eq
    _ = (w.map freeLetter).map
        (GGT.RelLetter.base : FreeGroup Generator →
          GGT.RelLetter (FreeGroup Generator) PEmpty) :=
      congrArg (List.map (GGT.RelLetter.base : FreeGroup Generator →
        GGT.RelLetter (FreeGroup Generator) PEmpty)) hboundary
    _ = relativeWord w := hrelative w

/-! ## Clean retyping interface -/

/-- The retyping fields needed by the Build module, expressed on the clean
vk closure.  It is intentionally separate from the landed
`VanKampen.CactusRelatorRetyping`, whose current module also imports the
repairing generic surgery file. -/
structure CleanCactusRelatorRetyping
    (Delta : VanKampen.DiscDiagram.{0, 0, 0}
      (triangleRelatorWords T)) where
  diagram : VanKampen.DiscDiagram.{0, 0, 0}
    (triangleRelatorWords T)
  boundaryWord_eq : diagram.boundaryWord = Delta.boundaryWord
  relatorOnly : RelatorOnly T diagram
  rCellCount_le : diagram.rCellCount ≤ Delta.rCellCount
  reduced : diagram.Reduced
  planar : diagram.toCombMap.IsPlanar

/-- The clean availability shape for the base-cell retyping step. -/
def CactusRelatorRetypingAvailability : Prop :=
  ∀ (Delta : VanKampen.DiscDiagram.{0, 0, 0}
    (triangleRelatorWords T)),
    Delta.Reduced → Nonempty (CleanCactusRelatorRetyping (T := T) Delta)

/-- A diagram already carrying relator-only coverage is a degenerate cactus
retyping: the identity diagram preserves its boundary, area, reducedness, and
planarity. -/
def cleanCactusRelatorRetyping_of_relatorOnly
    (Delta : VanKampen.DiscDiagram.{0, 0, 0}
      (triangleRelatorWords T))
    (hcover : RelatorOnly T Delta) (hred : Delta.Reduced)
    (hplanar : Delta.toCombMap.IsPlanar) :
    Nonempty (CleanCactusRelatorRetyping (T := T) Delta) := by
  exact ⟨{
    diagram := Delta
    boundaryWord_eq := rfl
    relatorOnly := hcover
    rCellCount_le := le_rfl
    reduced := hred
    planar := hplanar }⟩

theorem cactusRelatorRetypingAvailability_of_relatorOnly
    (hcover : ∀ (Delta : VanKampen.DiscDiagram.{0, 0, 0}
      (triangleRelatorWords T)),
      RelatorOnly T Delta)
    (hplanar : ∀ (Delta : VanKampen.DiscDiagram.{0, 0, 0}
      (triangleRelatorWords T)), Delta.toCombMap.IsPlanar) :
    CactusRelatorRetypingAvailability (T := T) := by
  intro Delta hred
  exact cleanCactusRelatorRetyping_of_relatorOnly (T := T) Delta
    (hcover Delta) hred (hplanar Delta)

/-! ## Empty free-group model tests -/

def emptyTriangleTable : PEmpty → TriangularHodgeLayer.Triangle PEmpty :=
  PEmpty.elim

theorem orientedCactusBoundaryProducer_empty_model :
    OrientedCactusBoundaryProducer (T := emptyTriangleTable) := by
  intro w _ hfree
  have hfreeOne : (w.map freeLetter).prod = (1 : FreeGroup PEmpty) :=
    Subsingleton.elim _ _
  exact (hfree hfreeOne).elim

theorem cactusDiscDiagramProducer_empty_model :
    CactusDiscDiagramProducer (T := emptyTriangleTable) := by
  intro w hw hfree
  exact (hfree (Subsingleton.elim _ _)).elim

end Table
end KazhdanHypGirthEightCactusProducer
end GGT
end GroupApproximation
