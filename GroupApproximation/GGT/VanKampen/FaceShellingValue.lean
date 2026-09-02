import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue

/-!
# The value of a shelled region boundary

`FaceShelling` peels a face set off a closed dart word one face at a time, each
step replacing an arc by the complementary arc of a face boundary.  When the
peeled faces are `G`-cells the word's value is unchanged, which is what
`GRegionBoundaryValue` already uses.  This file computes the value in general.

One peel step multiplies the value on the left by a conjugate of the peeled
face's value, with a conjugator read off the step: the value of the part of the
word before the arc, times the inverse of the value of the rotated prefix of the
face boundary.  So a shelling of a closed word down to the empty word writes its
value as an ordered product of conjugated face values, which is the van Kampen
product formula for the region the shelling peels.

`CellShelling` is `FaceShelling` with those conjugators recorded, so a producer
that supplies a shelling whose recorded cells are a given ordered list of based
relator cells gets the product formula for exactly that list.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w v

namespace Embedded

/-! ## Rotation conjugates the value of a dart word -/

/-- Reading a dart word backwards along reversed darts inverts its value. -/
theorem listVal_dartWord_invDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (darts : List Delta.toCombMap.Dart) :
    GGT.RelLetter.listVal (dartWord Delta (invDarts Delta darts)) =
      (GGT.RelLetter.listVal (dartWord Delta darts))⁻¹ :=
  listVal_dartWord_reverse_alpha Delta darts

/-- A cyclic rotation names the conjugate of what the word names, by the value
of the prefix that was moved. -/
theorem listVal_dartWord_rotate
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (darts : List Delta.toCombMap.Dart) (k : ℕ) :
    GGT.RelLetter.listVal (dartWord Delta (darts.rotate k)) =
      (GGT.RelLetter.listVal
          (dartWord Delta (darts.take (k % darts.length))))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta darts) *
        GGT.RelLetter.listVal
          (dartWord Delta (darts.take (k % darts.length))) := by
  have hsplit : darts.rotate k =
      darts.drop (k % darts.length) ++ darts.take (k % darts.length) :=
    List.rotate_eq_drop_append_take_mod
  have hval : GGT.RelLetter.listVal (dartWord Delta darts) =
      GGT.RelLetter.listVal (dartWord Delta (darts.take (k % darts.length))) *
        GGT.RelLetter.listVal
          (dartWord Delta (darts.drop (k % darts.length))) := by
    conv_lhs => rw [← List.take_append_drop (k % darts.length) darts]
    rw [dartWord_append, RelWord.listVal_append]
  rw [hsplit, dartWord_append, RelWord.listVal_append, hval]
  group

/-! ## One peel step -/

/-- The conjugator contributed by one peel step. -/
noncomputable def shellConjugator
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (face : Delta.toCombMap.Face)
    (before : List Delta.toCombMap.Dart) (k : ℕ) : G :=
  GGT.RelLetter.listVal (dartWord Delta before) *
    (GGT.RelLetter.listVal (dartWord Delta
      ((Delta.faceBoundary face).darts.take
        (k % (Delta.faceBoundary face).darts.length))))⁻¹

/-- Peeling one face multiplies the value of the word on the left by the
conjugate of the face's value. -/
theorem listVal_dartWord_shellStep
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (face : Delta.toCombMap.Face)
    (before arc after exposed : List Delta.toCombMap.Dart) (k : ℕ)
    (hrot : (Delta.faceBoundary face).darts.rotate k =
      exposed ++ invDarts Delta arc) :
    GGT.RelLetter.listVal (dartWord Delta (before ++ exposed ++ after)) =
      shellConjugator Delta face before k *
        GGT.RelLetter.listVal (Delta.faceWord face) *
        (shellConjugator Delta face before k)⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta (before ++ arc ++ after)) := by
  have hfw : GGT.RelLetter.listVal (Delta.faceWord face) =
      GGT.RelLetter.listVal
        (dartWord Delta (Delta.faceBoundary face).darts) := rfl
  have hu := listVal_dartWord_rotate Delta (Delta.faceBoundary face).darts k
  rw [hrot, dartWord_append, RelWord.listVal_append,
    listVal_dartWord_invDarts] at hu
  have hexposed : GGT.RelLetter.listVal (dartWord Delta exposed) =
      (GGT.RelLetter.listVal (dartWord Delta
          ((Delta.faceBoundary face).darts.take
            (k % (Delta.faceBoundary face).darts.length))))⁻¹ *
        GGT.RelLetter.listVal
          (dartWord Delta (Delta.faceBoundary face).darts) *
        GGT.RelLetter.listVal (dartWord Delta
          ((Delta.faceBoundary face).darts.take
            (k % (Delta.faceBoundary face).darts.length))) *
        GGT.RelLetter.listVal (dartWord Delta arc) := by
    calc GGT.RelLetter.listVal (dartWord Delta exposed)
        = GGT.RelLetter.listVal (dartWord Delta exposed) *
            (GGT.RelLetter.listVal (dartWord Delta arc))⁻¹ *
            GGT.RelLetter.listVal (dartWord Delta arc) := by group
      _ = ((GGT.RelLetter.listVal (dartWord Delta
              ((Delta.faceBoundary face).darts.take
                (k % (Delta.faceBoundary face).darts.length))))⁻¹ *
            GGT.RelLetter.listVal
              (dartWord Delta (Delta.faceBoundary face).darts) *
            GGT.RelLetter.listVal (dartWord Delta
              ((Delta.faceBoundary face).darts.take
                (k % (Delta.faceBoundary face).darts.length)))) *
            GGT.RelLetter.listVal (dartWord Delta arc) := by rw [hu]
      _ = _ := by group
  rw [dartWord_append, dartWord_append, RelWord.listVal_append,
    RelWord.listVal_append, dartWord_append, dartWord_append,
    RelWord.listVal_append, RelWord.listVal_append, hexposed, hfw,
    shellConjugator]
  group

/-! ## Shellings with their conjugators recorded -/

/-- A shelling of a closed dart word together with the conjugator each peel
step contributes. -/
inductive CellShelling {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) :
    List G → List Delta.toCombMap.Face → List Delta.toCombMap.Dart → Prop
  | empty : CellShelling Delta faces [] [] []
  | step {gs : List G} {l : List Delta.toCombMap.Face}
      {before arc after exposed : List Delta.toCombMap.Dart}
      (face : Delta.toCombMap.Face) (hface : face ∈ faces) (k : ℕ) (g : G)
      (hrot : (Delta.faceBoundary face).darts.rotate k =
        exposed ++ invDarts Delta arc)
      (hg : g = shellConjugator Delta face before k)
      (rest : CellShelling Delta faces gs l (before ++ arc ++ after)) :
      CellShelling Delta faces (g :: gs) (face :: l)
        (before ++ exposed ++ after)

/-- Forgetting the conjugators returns a shelling. -/
theorem cellShelling_toShelling
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    {gs : List G} {l : List Delta.toCombMap.Face}
    {cycle : List Delta.toCombMap.Dart}
    (h : CellShelling Delta faces gs l cycle) :
    FaceShelling Delta faces l cycle := by
  induction h with
  | empty => exact FaceShelling.empty
  | @step gs l before arc after exposed face hface k g hrot hg rest ih =>
      exact FaceShelling.step face hface k hrot ih

/-- **The van Kampen product formula for a shelled region.**  The value of a
shelled closed word is the ordered product of the conjugated values of the faces
peeled off it. -/
theorem listVal_dartWord_of_cellShelling
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    {gs : List G} {l : List Delta.toCombMap.Face}
    {cycle : List Delta.toCombMap.Dart}
    (h : CellShelling Delta faces gs l cycle) :
    GGT.RelLetter.listVal (dartWord Delta cycle) =
      (List.zipWith
        (fun g f => g * GGT.RelLetter.listVal (Delta.faceWord f) * g⁻¹)
        gs l).prod := by
  induction h with
  | empty => rfl
  | @step gs l before arc after exposed face hface k g hrot hg rest ih =>
      rw [List.zipWith_cons_cons, List.prod_cons, ← ih, hg]
      exact listVal_dartWord_shellStep Delta face before arc after exposed k
        hrot

end Embedded
end VanKampen
end GGT
end GroupApproximation
