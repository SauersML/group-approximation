import GroupApproximation.GGT.KazhdanHypGirthEightVKInterface
import GroupApproximation.GGT.VanKampen.BoundaryFarthestPoint

/-!
# The finite far-point boundary producer

`BoundaryFarthestPoint` is the finite part of the far-point argument.  It
chooses a maximum of a supplied vertex weight on the duplicate-free outer
boundary and exposes the two boundary arcs at that occurrence.  This module
packages that certificate next to the exact girth-eight word shape without
importing the repairing higher-level primitives.

The remaining source is intentionally explicit: the current vk records do not
contain a map from the two geodesic inequalities to a labelled reduced disc
diagram.  Once such a source supplies a diagram, `of_diagram` constructs the
far-point certificate by the finite maximum theorem rather than assuming it.
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypGirthEightFarPointProducer

open GroupApproximation.KazhdanHyp
open GroupApproximation.GGT.GirthEightVKInterface
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-- The free-group letter belonging to a signed generator. -/
def freeLetter (u : TriangularHodgeLayer.SignedGenerator Generator) :
    FreeGroup Generator :=
  FoxBoundary.letterValue FreeGroup.of u

/-- The presented-group triviality condition on a literal signed word. -/
def PresentedWordIsTrivial
    (w : List (TriangularHodgeLayer.SignedGenerator Generator)) : Prop :=
  PresentedGroup.mk
      (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
      (PresentedGroupRelatorReplay.word w) = 1

/-- The word-only conclusion consumed by the slim-triangle build. -/
def FarPointBoundaryWord : Prop :=
  ∀ (delta : ℕ) (x y z p : TriangularHodgeLayer.Presented T),
    Hyperbolic.IsBetween
      (↑(GirthEightSlim.presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) x p y →
    (∀ q : TriangularHodgeLayer.Presented T,
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) x q z →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    (∀ q : TriangularHodgeLayer.Presented T,
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) z q y →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    ∃ w : List (TriangularHodgeLayer.SignedGenerator Generator),
      PresentedWordIsTrivial (T := T) w ∧
        (w.map freeLetter).prod ≠ 1

/-- A word and a reduced diagram, together with a vertex weight, form the
source data from which the finite far-point certificate is constructed. -/
structure BoundaryWordFarPointWitness
    (Delta : VanKampen.DiscDiagram.{0, 0, 0}
      (triangleRelatorWords T)) where
  word : List (TriangularHodgeLayer.SignedGenerator Generator)
  trivial : PresentedWordIsTrivial (T := T) word
  free_nontrivial : (word.map freeLetter).prod ≠ 1
  boundary_eq : Delta.boundaryWord =
    (word.map freeLetter).map
      (GGT.RelLetter.base : FreeGroup Generator →
        GGT.RelLetter (FreeGroup Generator) PEmpty)
  reduced : Delta.Reduced
  weight : Delta.toCombMap.Vertex → ℕ
  farthest : BoundaryFarthestPoint
    (Delta.faceBoundary Delta.outerFace) weight

namespace BoundaryWordFarPointWitness

/-- A reduced diagram with a boundary spelling and a supplied weight obtains
the maximum point and its two arcs by the finite boundary theorem. -/
noncomputable def of_diagram
    (word : List (TriangularHodgeLayer.SignedGenerator Generator))
    (Delta : VanKampen.DiscDiagram.{0, 0, 0}
      (triangleRelatorWords T))
    (htrivial : PresentedWordIsTrivial (T := T) word)
    (hfree : (word.map freeLetter).prod ≠ 1)
    (hboundary : Delta.boundaryWord =
      (word.map freeLetter).map
        (GGT.RelLetter.base : FreeGroup Generator →
          GGT.RelLetter (FreeGroup Generator) PEmpty))
    (hred : Delta.Reduced)
    (weight : Delta.toCombMap.Vertex → ℕ) :
    Nonempty (BoundaryWordFarPointWitness (T := T) Delta) := by
  obtain ⟨farthest⟩ :=
    VanKampen.farthestBoundaryPoint_of_discDiagram (Delta := Delta) weight
  exact ⟨{
    word := word
    trivial := htrivial
    free_nontrivial := hfree
    boundary_eq := hboundary
    reduced := hred
    weight := weight
    farthest := farthest }⟩

end BoundaryWordFarPointWitness

/-- The exact missing source: it supplies a labelled reduced diagram and a
vertex weight for every geodesic configuration.  Its far-point certificate is
then constructed, not postulated. -/
def FarPointBoundaryWitnessSource : Prop :=
  ∀ (delta : ℕ) (x y z p : TriangularHodgeLayer.Presented T),
    Hyperbolic.IsBetween
      (↑(GirthEightSlim.presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) x p y →
    (∀ q : TriangularHodgeLayer.Presented T,
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) x q z →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    (∀ q : TriangularHodgeLayer.Presented T,
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) z q y →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    ∃ (word : List (TriangularHodgeLayer.SignedGenerator Generator))
      (Delta : VanKampen.DiscDiagram.{0, 0, 0}
        (triangleRelatorWords T))
      (weight : Delta.toCombMap.Vertex → ℕ),
      PresentedWordIsTrivial (T := T) word ∧
      (word.map freeLetter).prod ≠ 1 ∧
      Delta.boundaryWord =
        (word.map freeLetter).map
          (GGT.RelLetter.base : FreeGroup Generator →
            GGT.RelLetter (FreeGroup Generator) PEmpty) ∧
      Delta.Reduced

/-- A witness source implies the exact word-only far-point proposition. -/
theorem farPointBoundaryWord_of_witnessSource
    (hsource : FarPointBoundaryWitnessSource (T := T)) :
    FarPointBoundaryWord (T := T) := by
  intro delta x y z p hp hfarXZ hfarZY
  obtain ⟨word, Delta, weight, htrivial, hfree, hboundary, hred⟩ :=
    hsource delta x y z p hp hfarXZ hfarZY
  obtain ⟨W⟩ := BoundaryWordFarPointWitness.of_diagram word Delta
    htrivial hfree hboundary hred weight
  exact ⟨W.word, W.trivial, W.free_nontrivial⟩

/-! ## Finite model -/

theorem oneTriangle_farthest_model
    (weight : VanKampen.oneTriangleCombMap.Vertex → ℕ) :
    Nonempty (VanKampen.BoundaryFarthestPoint
      (VanKampen.FaceBoundary.based VanKampen.oneTriangleCombMap
        (0, false)) weight) :=
  VanKampen.oneTriangle_farthestBoundaryPoint_model weight

end Table
end KazhdanHypGirthEightFarPointProducer
end GGT
end GroupApproximation
