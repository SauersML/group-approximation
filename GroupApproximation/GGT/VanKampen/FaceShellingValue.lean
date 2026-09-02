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

The peel step does not use that the peeled word is a face boundary, so it is
proved for an arbitrary closed word and both orientations of a face are
instances of it.  `CellShelling` records the conjugator and the oriented word of
each step, so a producer supplying a shelling whose recorded steps are a given
ordered list of based relator cells gets the product formula for exactly that
list, whichever way each cell is based.
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

/-- The conjugator contributed by peeling the word `cellDarts` at rotation
`k` out of a word whose part before the replaced arc is `before`. -/
noncomputable def shellConjugatorOn
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (cellDarts before : List Delta.toCombMap.Dart) (k : ℕ) : G :=
  GGT.RelLetter.listVal (dartWord Delta before) *
    (GGT.RelLetter.listVal
      (dartWord Delta (cellDarts.take (k % cellDarts.length))))⁻¹

/-- Peeling one closed word multiplies the value of the word on the left by the
conjugate of the peeled word's value. -/
theorem listVal_dartWord_shellStepOn
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (cellDarts before arc after exposed : List Delta.toCombMap.Dart) (k : ℕ)
    (hrot : cellDarts.rotate k = exposed ++ invDarts Delta arc) :
    GGT.RelLetter.listVal (dartWord Delta (before ++ exposed ++ after)) =
      shellConjugatorOn Delta cellDarts before k *
        GGT.RelLetter.listVal (dartWord Delta cellDarts) *
        (shellConjugatorOn Delta cellDarts before k)⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta (before ++ arc ++ after)) := by
  have hu := listVal_dartWord_rotate Delta cellDarts k
  rw [hrot, dartWord_append, RelWord.listVal_append,
    listVal_dartWord_invDarts] at hu
  have hexposed : GGT.RelLetter.listVal (dartWord Delta exposed) =
      (GGT.RelLetter.listVal
          (dartWord Delta (cellDarts.take (k % cellDarts.length))))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta cellDarts) *
        GGT.RelLetter.listVal
          (dartWord Delta (cellDarts.take (k % cellDarts.length))) *
        GGT.RelLetter.listVal (dartWord Delta arc) := by
    calc GGT.RelLetter.listVal (dartWord Delta exposed)
        = GGT.RelLetter.listVal (dartWord Delta exposed) *
            (GGT.RelLetter.listVal (dartWord Delta arc))⁻¹ *
            GGT.RelLetter.listVal (dartWord Delta arc) := by group
      _ = ((GGT.RelLetter.listVal
              (dartWord Delta (cellDarts.take (k % cellDarts.length))))⁻¹ *
            GGT.RelLetter.listVal (dartWord Delta cellDarts) *
            GGT.RelLetter.listVal
              (dartWord Delta (cellDarts.take (k % cellDarts.length)))) *
            GGT.RelLetter.listVal (dartWord Delta arc) := by rw [hu]
      _ = _ := by group
  rw [dartWord_append, dartWord_append, RelWord.listVal_append,
    RelWord.listVal_append, dartWord_append, dartWord_append,
    RelWord.listVal_append, RelWord.listVal_append, hexposed,
    shellConjugatorOn]
  group

/-! ## The two orientations of a face -/

/-- The boundary of a face, read either way round. -/
noncomputable def orientedFaceDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (face : Delta.toCombMap.Face)
    (rev : Bool) : List Delta.toCombMap.Dart :=
  if rev then invDarts Delta (Delta.faceBoundary face).darts
    else (Delta.faceBoundary face).darts

/-- Reading a face boundary the other way round inverts the face word's
value. -/
theorem listVal_orientedFaceDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (face : Delta.toCombMap.Face)
    (rev : Bool) :
    GGT.RelLetter.listVal (dartWord Delta (orientedFaceDarts Delta face rev)) =
      (if rev then (GGT.RelLetter.listVal (Delta.faceWord face))⁻¹
        else GGT.RelLetter.listVal (Delta.faceWord face)) := by
  cases rev
  · rfl
  · exact listVal_dartWord_invDarts Delta (Delta.faceBoundary face).darts

/-! ## Shellings with their steps recorded -/

/-- A shelling of a closed dart word together with, for each peel step, the
conjugator it contributes and the oriented face boundary it peels. -/
inductive CellShelling {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) :
    List G → List (List Delta.toCombMap.Dart) →
      List Delta.toCombMap.Dart → Prop
  | empty : CellShelling Delta faces [] [] []
  | step {gs : List G} {cds : List (List Delta.toCombMap.Dart)}
      {before arc after exposed : List Delta.toCombMap.Dart}
      (face : Delta.toCombMap.Face) (hface : face ∈ faces) (rev : Bool)
      (k : ℕ) (g : G) (cd : List Delta.toCombMap.Dart)
      (hcd : cd = orientedFaceDarts Delta face rev)
      (hrot : cd.rotate k = exposed ++ invDarts Delta arc)
      (hg : g = shellConjugatorOn Delta cd before k)
      (rest : CellShelling Delta faces gs cds (before ++ arc ++ after)) :
      CellShelling Delta faces (g :: gs) (cd :: cds)
        (before ++ exposed ++ after)

/-- **The van Kampen product formula for a shelled region.**  The value of a
shelled closed word is the ordered product of the conjugated values of the
words peeled off it. -/
theorem listVal_dartWord_of_cellShelling
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    {gs : List G} {cds : List (List Delta.toCombMap.Dart)}
    {cycle : List Delta.toCombMap.Dart}
    (h : CellShelling Delta faces gs cds cycle) :
    GGT.RelLetter.listVal (dartWord Delta cycle) =
      (List.zipWith
        (fun g cd => g * GGT.RelLetter.listVal (dartWord Delta cd) * g⁻¹)
        gs cds).prod := by
  induction h with
  | empty => rfl
  | @step gs cds before arc after exposed face hface rev k g cd hcd hrot hg
      rest ih =>
      rw [List.zipWith_cons_cons, List.prod_cons, ← ih, hg]
      exact listVal_dartWord_shellStepOn Delta cd before arc after exposed k
        hrot

end Embedded
end VanKampen
end GGT
end GroupApproximation
