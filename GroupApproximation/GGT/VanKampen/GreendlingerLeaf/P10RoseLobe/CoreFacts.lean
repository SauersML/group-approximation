import GroupApproximation.GGT.VanKampen.ClosedWalkFirstTurnEnclosure
import GroupApproximation.GGT.VanKampen.CombMapRestrictionPlanarity
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbitClass
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCycClass
import GroupApproximation.Meta.AxiomGuard

/-!
# The planar facts about the walk map of a pocket

Lane gl-p10-60.  Notation: `M = X.toCombMap`, `c = K.boundary.cycle` (a closed walk, `hK`),
`R = FaceClassStep M (walkKeep M c)` (advance around a face of `M`, or cross an edge off the walk)
and `Γ = walkMap M c`, the map on the edges of the walk (rotation: first return of `σ`).  The face
classes of `R` are the regions of the sphere cut along `c`; the lobe colourings of
`roseLobeNoBub_Statement` are unions of them.  This module proves, from the planarity of the disc
diagram alone, the four facts that `roseLobeCore_Statement` (`CoreStatement`) hands to the planar
core:

* `roseLobeCore_planar`: `Γ` is connected with Euler characteristic `2`
  (`IsRestriction.planar`, `FirstTurnEnclosure.walkMap_connected`);
* `roseLobeCore_iff` (Jordan separation): two darts of `Γ` are `R`-equivalent iff they lie on
  one face of `Γ`.  `(⇒)` is `IsRestriction.faceOf_eq_of_faceClass`; `(⇐)` follows the face
  permutation of `Γ`, one first-return run at a time (`PocketOrbit.keepMap_facePerm_eqvGen`);
* `roseLobeCore_cover` (cover): every `R`-class holds a dart of `Γ`
  (`P01HoldingSmallFaces.exists_keep_of_connected`);
* `roseLobeCore_side`: `faceOf x ∈ K.faces` is constant on `R`-classes
  (`P10ExtremalRegion.extremalJordanPickCyc_faces_iff`).

So the regions of `c` are exactly the faces of the planar map `Γ`, each lying inside or outside
`K.faces`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The walk map of a closed-walk pocket is connected.** -/
theorem roseLobeCore_conn (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk) :
    (walkMap X.toCombMap K.boundary.cycle).IsConnected :=
  FirstTurnEnclosure.walkMap_connected K.boundary.cycle_nonempty hK.1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_conn

/-- **The walk map of a closed-walk pocket is planar**: connected, Euler characteristic `2`. -/
theorem roseLobeCore_planar (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk) :
    (walkMap X.toCombMap K.boundary.cycle).IsPlanar :=
  (walkMap_isRestriction X.toCombMap K.boundary.cycle).planar X.planar
    (roseLobeCore_conn K hK)
    ⟨K.boundary.cycle.head K.boundary.cycle_nonempty,
      Or.inl (List.head_mem K.boundary.cycle_nonempty)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_planar

/-- **Separation**: two darts of the walk map joined by face moves and crossings off the walk lie
on one face of the walk map. -/
theorem roseLobeCore_sep (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    {x y : (walkMap X.toCombMap K.boundary.cycle).Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle)) x.1 y.1) :
    (walkMap X.toCombMap K.boundary.cycle).faceOf x =
      (walkMap X.toCombMap K.boundary.cycle).faceOf y := by
  have h' : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (· ∈ Set.range (Function.Embedding.subtype (walkKeep X.toCombMap K.boundary.cycle))))
      x.1 y.1 :=
    SimpleClosedWalkSides.faceClass_mono X.toCombMap
      (fun z hz => by rintro ⟨z', rfl⟩; exact hz z'.2) h
  exact (walkMap_isRestriction X.toCombMap K.boundary.cycle).faceOf_eq_of_faceClass
    X.planar (roseLobeCore_conn K hK) (d := x) (d' := y) h'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_sep

/-- The powers of the face permutation of the walk map stay in the face class. -/
theorem roseLobeCore_pow (K : PocketFaceSet D eps X lo hi)
    (x : (walkMap X.toCombMap K.boundary.cycle).Dart) (m : ℕ) :
    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle)) x.1
      (((walkMap X.toCombMap K.boundary.cycle).facePerm ^ m) x).1 := by
  induction m with
  | zero => exact P01HoldingSmallFaces.eqvGen_of_eq (by rw [pow_zero, Equiv.Perm.one_apply])
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact Relation.EqvGen.trans _ _ _ ih
      (P07InnerPocket.PocketOrbit.keepMap_facePerm_eqvGen (M := X.toCombMap)
        (keep := walkKeep X.toCombMap K.boundary.cycle)
        (walkKeep_alpha X.toCombMap K.boundary.cycle) _)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_pow

/-- Two darts on one face of the walk map are in one face class. -/
theorem roseLobeCore_unsep (K : PocketFaceSet D eps X lo hi)
    {x y : (walkMap X.toCombMap K.boundary.cycle).Dart}
    (h : (walkMap X.toCombMap K.boundary.cycle).faceOf x =
      (walkMap X.toCombMap K.boundary.cycle).faceOf y) :
    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle)) x.1 y.1 := by
  obtain ⟨n, hn⟩ :=
    (((walkMap X.toCombMap K.boundary.cycle).faceOf_eq_iff x y).mp h).exists_nat_pow_eq
  rw [← hn]
  exact roseLobeCore_pow K x n

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_unsep
