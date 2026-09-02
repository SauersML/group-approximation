import GroupApproximation.GGT.VanKampen.DiscDiagram

/-!
# Core definitions for face-set word moves

These four inductives and one definition are exactly the face-set move
vocabulary, with no theorems.  They live here, above
`Estimating/Embedded.lean`, so that `Embedded.Contiguity` can carry a shelling
of its own boundary cycle as a producer-supplied field.

Every theorem about them stays where it was, so no consumer moves and no name
changes.  Nothing here mentions `dartWord`, `FaceSetBoundary` or any estimating
notion, which is what lets the file sit this high.

## Import hygiene

This file imports `VanKampen/DiscDiagram` and nothing else.  That is already a
direct import of `Estimating/Embedded.lean`, so the new edge cannot close a
cycle: if `DiscDiagram`'s closure contained `Estimating/Embedded` or
`Estimating/Selection`, the existing graph would already be cyclic.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

namespace Embedded

/-- The reverse-orientation dart list: the order is reversed and every dart is
replaced by its `alpha`-reverse.  This is the word-level inverse of a dart
list. -/
def invDarts {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (darts : List Delta.toCombMap.Dart) : List Delta.toCombMap.Dart :=
  darts.reverse.map Delta.toCombMap.alpha

/-- Finite word moves used when a planar union of faces is pasted into its
single exterior boundary.  A selected complete face and an immediate
`alpha`-pair are the two elementary deletions. -/
inductive FaceSetWordHomotopy
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) :
    List Delta.toCombMap.Dart → List Delta.toCombMap.Dart → Prop
  | refl (word) : FaceSetWordHomotopy Delta faces word word
  | eraseFace (face : Delta.toCombMap.Face) (hface : face ∈ faces)
      (before after : List Delta.toCombMap.Dart) :
      FaceSetWordHomotopy Delta faces
        (before ++ (Delta.faceBoundary face).darts ++ after)
        (before ++ after)
  | eraseAlphaPair (dart : Delta.toCombMap.Dart)
      (before after : List Delta.toCombMap.Dart) :
      FaceSetWordHomotopy Delta faces
        (before ++ dart :: Delta.toCombMap.alpha dart :: after)
        (before ++ after)
  | symm {first second} :
      FaceSetWordHomotopy Delta faces first second →
        FaceSetWordHomotopy Delta faces second first
  | trans {first second third} :
      FaceSetWordHomotopy Delta faces first second →
      FaceSetWordHomotopy Delta faces second third →
        FaceSetWordHomotopy Delta faces first third

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- One elementary move in a boundary peel.  The two insertion constructors
are the symmetric forms of the deletion generators; naming them explicitly
makes the ``insert the remaining face boundary, then cancel internal
`alpha`-pairs'' factorisation available to geometric producers. -/
inductive FaceSetElementaryMove
    {faces : Finset Delta.toCombMap.Face} :
    List Delta.toCombMap.Dart → List Delta.toCombMap.Dart → Prop
  | eraseFace (face : Delta.toCombMap.Face) (hface : face ∈ faces)
      (before after : List Delta.toCombMap.Dart) :
      FaceSetElementaryMove
        (before ++ (Delta.faceBoundary face).darts ++ after)
        (before ++ after)
  | insertFace (face : Delta.toCombMap.Face) (hface : face ∈ faces)
      (before after : List Delta.toCombMap.Dart) :
      FaceSetElementaryMove
        (before ++ after)
        (before ++ (Delta.faceBoundary face).darts ++ after)
  | eraseAlphaPair (dart : Delta.toCombMap.Dart)
      (before after : List Delta.toCombMap.Dart) :
      FaceSetElementaryMove
        (before ++ dart :: Delta.toCombMap.alpha dart :: after)
        (before ++ after)
  | insertAlphaPair (dart : Delta.toCombMap.Dart)
      (before after : List Delta.toCombMap.Dart) :
      FaceSetElementaryMove
        (before ++ after)
        (before ++ dart :: Delta.toCombMap.alpha dart :: after)

/-- A finite sequence of elementary peel moves. -/
inductive FaceSetMoveSequence
    {faces : Finset Delta.toCombMap.Face} :
    List Delta.toCombMap.Dart → List Delta.toCombMap.Dart → Prop
  | refl (word : List Delta.toCombMap.Dart) :
      FaceSetMoveSequence word word
  | cons {first second third : List Delta.toCombMap.Dart}
      (head : FaceSetElementaryMove (faces := faces) first second)
      (tail : FaceSetMoveSequence (faces := faces) second third) :
      FaceSetMoveSequence first third

/-- A shelling of a selected face set: an ordering of faces in which each new
face attaches to the current walk along one arc, which may be empty. -/
inductive FaceShelling {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) :
    List Delta.toCombMap.Face → List Delta.toCombMap.Dart → Prop
  | empty : FaceShelling Delta faces [] []
  | step {l : List Delta.toCombMap.Face}
      {before arc after exposed : List Delta.toCombMap.Dart}
      (face : Delta.toCombMap.Face) (hface : face ∈ faces) (k : ℕ)
      (hrot : (Delta.faceBoundary face).darts.rotate k =
        exposed ++ invDarts Delta arc)
      (rest : FaceShelling Delta faces l (before ++ arc ++ after)) :
      FaceShelling Delta faces (face :: l) (before ++ exposed ++ after)

end Embedded

end VanKampen
end GGT
end GroupApproximation
