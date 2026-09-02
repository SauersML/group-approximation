import GroupApproximation.GGT.VanKampen.CactusTopology

/-!
# Reclosing a disc region in a combinatorial map

This file contains the topology-only part of relative diagram surgery.  For a
selected set of faces, every edge whose two sides lie in the set is deleted.
The remaining darts split into darts based in unselected faces and boundary
darts based in the selected region.  The old face permutation is retained on
the first summand, while a supplied duplicate-free boundary cycle gives the
new permutation on the second.  Vertex rotation is then recovered from the
new face permutation and the restricted edge reversal.

The boundary-cycle data by itself does not express that the selected union is
a topological disc.  `IsDiscRegion` records the two precise consequences used
by the ambient planar diagram: connectedness of the reclosed map and
preservation of Euler characteristic.  With those fields, planarity of
`replaceGRegion` is a theorem.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Surgery
namespace MapCollapse

universe v

/-- A dart is internal to a face set when both orientations of its edge are
based in selected faces. -/
def InternalDart (M : CombMap) (faces : Finset M.Face) (d : M.Dart) : Prop :=
  M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∈ faces

/-- The darts retained after deleting every edge internal to the region. -/
abbrev KeptDart (M : CombMap) (faces : Finset M.Face) :=
  {d : M.Dart // ¬ InternalDart M faces d}

noncomputable instance keptDartFintype (M : CombMap)
    (faces : Finset M.Face) : Fintype (KeptDart M faces) :=
  Fintype.ofFinite _

/-- Darts based outside the selected face set. -/
abbrev OutsideDart (M : CombMap) (faces : Finset M.Face) :=
  {d : M.Dart // M.faceOf d ∉ faces}

/-- Darts on the selected side of the face-set boundary. -/
def IsBoundaryDart (M : CombMap) (faces : Finset M.Face)
    (d : M.Dart) : Prop :=
  M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces

/-- The subtype of oriented boundary darts. -/
abbrev BoundaryDart (M : CombMap) (faces : Finset M.Face) :=
  {d : M.Dart // IsBoundaryDart M faces d}

/-- Reversing an edge preserves the internal-dart predicate. -/
theorem internalDart_alpha_iff (M : CombMap) (faces : Finset M.Face)
    (d : M.Dart) :
    InternalDart M faces (M.alpha d) ↔ InternalDart M faces d := by
  constructor
  · rintro ⟨halpha, hdouble⟩
    rw [M.alpha_involutive d] at hdouble
    exact ⟨hdouble, halpha⟩
  · rintro ⟨hd, halpha⟩
    refine ⟨halpha, ?_⟩
    rw [M.alpha_involutive d]
    exact hd

/-- Edge reversal restricted to retained darts. -/
def keptAlpha (M : CombMap) (faces : Finset M.Face) :
    Equiv.Perm (KeptDart M faces) where
  toFun d := ⟨M.alpha d, by
    simpa only [internalDart_alpha_iff] using d.property⟩
  invFun d := ⟨M.alpha d, by
    simpa only [internalDart_alpha_iff] using d.property⟩
  left_inv d := by
    apply Subtype.ext
    exact M.alpha_involutive d.1
  right_inv d := by
    apply Subtype.ext
    exact M.alpha_involutive d.1

/-- The restricted edge reversal is involutive. -/
theorem keptAlpha_involutive (M : CombMap) (faces : Finset M.Face) :
    Function.Involutive (keptAlpha M faces) := by
  intro d
  apply Subtype.ext
  exact M.alpha_involutive d.1

/-- The restricted edge reversal has no fixed dart. -/
theorem keptAlpha_fixedPointFree (M : CombMap) (faces : Finset M.Face)
    (d : KeptDart M faces) : keptAlpha M faces d ≠ d := by
  intro h
  apply M.alpha_fixedPointFree d.1
  exact congrArg Subtype.val h

/-- The old face permutation restricted to darts based outside the region. -/
def outsideFacePerm (M : CombMap) (faces : Finset M.Face) :
    Equiv.Perm (OutsideDart M faces) where
  toFun d := ⟨M.facePerm d, by
    rw [M.faceOf_facePerm]
    exact d.property⟩
  invFun d := ⟨M.facePerm.symm d, by
    have hface : M.faceOf (M.facePerm.symm d.1) = M.faceOf d.1 := by
      have h := M.faceOf_facePerm (M.facePerm.symm d.1)
      simpa only [M.facePerm.apply_symm_apply] using h.symm
    rw [hface]
    exact d.property⟩
  left_inv d := by
    apply Subtype.ext
    exact M.facePerm.symm_apply_apply d.1
  right_inv d := by
    apply Subtype.ext
    exact M.facePerm.apply_symm_apply d.1

/-- A duplicate-free cyclic enumeration of every oriented boundary dart. -/
structure BoundaryCycle (M : CombMap) (faces : Finset M.Face) where
  cycle : List M.Dart
  cycle_nonempty : cycle ≠ []
  cycle_nodup : cycle.Nodup
  cycle_mem_iff : ∀ d : M.Dart, d ∈ cycle ↔ IsBoundaryDart M faces d

namespace BoundaryCycle

/-- The list positions of a boundary cycle are equivalent to its boundary
dart subtype. -/
noncomputable def positionEquiv
    {M : CombMap} {faces : Finset M.Face}
    (boundary : BoundaryCycle M faces) :
    Fin boundary.cycle.length ≃ BoundaryDart M faces := by
  classical
  let memberEquiv : Fin boundary.cycle.length ≃
      {d : M.Dart // d ∈ boundary.cycle} :=
    boundary.cycle_nodup.getEquiv boundary.cycle
  have hpred : (fun d : M.Dart => d ∈ boundary.cycle) =
      (fun d : M.Dart => IsBoundaryDart M faces d) := by
    funext d
    exact propext (boundary.cycle_mem_iff d)
  exact memberEquiv.trans (Equiv.subtypeEquivProp hpred)

/-- Cyclic successor on the supplied oriented boundary enumeration. -/
noncomputable def boundaryPerm
    {M : CombMap} {faces : Finset M.Face}
    (boundary : BoundaryCycle M faces) :
    Equiv.Perm (BoundaryDart M faces) :=
  boundary.positionEquiv.symm.trans
    ((finRotate boundary.cycle.length).trans boundary.positionEquiv)

end BoundaryCycle

/-- Inverse of the retained-dart split, defined separately so its two
subtype proofs elaborate before the dependent conditional. -/
def keptSplitInv (M : CombMap) (faces : Finset M.Face) :
    OutsideDart M faces ⊕ BoundaryDart M faces → KeptDart M faces
  | Sum.inl d => ⟨d.1, by
      rw [InternalDart]
      exact fun hinternal => d.property hinternal.1⟩
  | Sum.inr d => ⟨d.1, by
      rw [InternalDart]
      exact fun hinternal => d.property.2 hinternal.2⟩

/-- Every retained dart is uniquely either based outside the region or is an
oriented boundary dart based inside it. -/
noncomputable def keptSplitEquiv (M : CombMap) (faces : Finset M.Face) :
    KeptDart M faces ≃ OutsideDart M faces ⊕ BoundaryDart M faces := by
  classical
  exact
    { toFun := fun d => if hface : M.faceOf d.1 ∈ faces then
        Sum.inr ⟨d.1, hface, fun halpha => d.property ⟨hface, halpha⟩⟩
      else Sum.inl ⟨d.1, hface⟩
      invFun := keptSplitInv M faces
      left_inv := fun d => by
        by_cases hface : M.faceOf d.1 ∈ faces
        · have halpha : M.faceOf (M.alpha d.1) ∉ faces := by
            intro halpha
            exact d.property ⟨hface, halpha⟩
          change keptSplitInv M faces (if _h : M.faceOf d.1 ∈ faces then
              Sum.inr ⟨d.1, _h, halpha⟩ else Sum.inl ⟨d.1, _h⟩) = d
          rw [dif_pos hface]
          apply Subtype.ext
          rfl
        · change keptSplitInv M faces (if _h : M.faceOf d.1 ∈ faces then
              Sum.inr ⟨d.1, _h, fun _halpha => (hface _h).elim⟩
            else Sum.inl ⟨d.1, _h⟩) = d
          rw [dif_neg hface]
          apply Subtype.ext
          rfl
      right_inv := fun part => by
        rcases part with outside | boundary
        · change (if hface : M.faceOf outside.1 ∈ faces then _ else _) = _
          rw [dif_neg outside.property]
          simp only [keptSplitInv]
        · change (if hface : M.faceOf boundary.1 ∈ faces then _ else _) = _
          rw [dif_pos boundary.property.1]
          simp only [keptSplitInv] }

/-- The new face permutation: old rotation on outside faces and the supplied
single cycle on the collapsed region. -/
noncomputable def reclosedFacePerm (M : CombMap) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) : Equiv.Perm (KeptDart M faces) :=
  (keptSplitEquiv M faces).trans
    ((Equiv.sumCongr (outsideFacePerm M faces) boundary.boundaryPerm).trans
      (keptSplitEquiv M faces).symm)

/-- Build a combinatorial map from edge reversal and a prescribed face
permutation.  Vertex rotation is forced to be `facePerm * alpha`. -/
def ofAlphaFacePerm
    {Dart : Type v} [Fintype Dart]
    (alpha facePerm : Equiv.Perm Dart)
    (alpha_involutive : Function.Involutive alpha)
    (alpha_fixedPointFree : ∀ d, alpha d ≠ d) : CombMap.{v} where
  Dart := Dart
  dartFintype := inferInstance
  alpha := alpha
  sigma := facePerm * alpha
  alpha_involutive := alpha_involutive
  alpha_fixedPointFree := alpha_fixedPointFree

/-- The map built from a prescribed face permutation has exactly that face
permutation. -/
theorem ofAlphaFacePerm_facePerm
    {Dart : Type v} [Fintype Dart]
    (alpha facePerm : Equiv.Perm Dart)
    (hinv : Function.Involutive alpha)
    (hfpf : ∀ d, alpha d ≠ d) :
    (ofAlphaFacePerm alpha facePerm hinv hfpf).facePerm = facePerm := by
  apply Equiv.ext
  intro d
  change (facePerm * alpha) (alpha d) = facePerm d
  rw [Equiv.Perm.mul_apply, hinv]

/-- Delete all internal edge pairs and reclose the selected region along its
single boundary cycle. -/
noncomputable def reclosedMap (M : CombMap) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) : CombMap where
  Dart := KeptDart M faces
  dartFintype := inferInstance
  alpha := keptAlpha M faces
  sigma := reclosedFacePerm M faces boundary * keptAlpha M faces
  alpha_involutive := keptAlpha_involutive M faces
  alpha_fixedPointFree := keptAlpha_fixedPointFree M faces

/-- The face permutation after reclosing is the piecewise outside/boundary
permutation constructed above. -/
theorem reclosedMap_facePerm (M : CombMap) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) :
    (reclosedMap M faces boundary).facePerm =
      reclosedFacePerm M faces boundary := by
  exact ofAlphaFacePerm_facePerm (keptAlpha M faces)
    (reclosedFacePerm M faces boundary) (keptAlpha_involutive M faces)
    (keptAlpha_fixedPointFree M faces)

/-- The topological disc condition required by the collapse. -/
structure IsDiscRegion (M : CombMap) (faces : Finset M.Face)
    extends BoundaryCycle M faces where
  reclosed_connected :
    (reclosedMap M faces toBoundaryCycle).IsConnected
  euler_preserved :
    (reclosedMap M faces toBoundaryCycle).eulerCharacteristic =
      M.eulerCharacteristic

/-- Replace the selected disc region by the single face bounded by its
oriented boundary cycle. -/
noncomputable def replaceGRegion (M : CombMap) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) : CombMap :=
  reclosedMap M faces region.toBoundaryCycle

/-- Replacing a disc region in a planar map is planar. -/
theorem replaceGRegion_planar (M : CombMap) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (hplanar : M.IsPlanar) :
    (replaceGRegion M faces region).IsPlanar := by
  constructor
  · exact region.reclosed_connected
  · change (reclosedMap M faces region.toBoundaryCycle).eulerCharacteristic = 2
    rw [region.euler_preserved]
    exact hplanar.2

/-- Planarity of the replacement exposes its connectedness separately. -/
theorem replaceGRegion_connected (M : CombMap) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) (hplanar : M.IsPlanar) :
    (replaceGRegion M faces region).IsConnected :=
  (replaceGRegion_planar M faces region hplanar).1

end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation
