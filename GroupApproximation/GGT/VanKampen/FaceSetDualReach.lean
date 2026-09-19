import GroupApproximation.GGT.VanKampen.FaceSetMoveAlgebra

/-!
# Connectivity of the selected-face dual

`FaceSetDualConnectivity.selectedFaces_connected` is not available: that module
does not compile, and its proof takes a boundary dart of the face *set* to be a
dart of a named face.  It need not be one, and for some selected faces no dart
of the face is a boundary dart at all — a face surrounded on every side by
selected faces contributes nothing to the boundary cycle.

This module proves the statement by a different route, and defines its own
`DualAdjacency` so that it does not depend on the broken file.  The key step is
`exists_boundaryDart_dualConnected`: every selected face is dual-connected to a
face which does carry a boundary dart.  The proof is a closure argument rather
than a path argument.  Suppose some selected face `f` reaches no boundary dart.
The faces selected and dual-connected to `f` then have the property that every
dart based in them has its reverse based in such a face too, so the set of darts
based in them is closed under `alpha` and under `sigma`, using
`faceOf (sigma x) = faceOf (alpha x)`.  Ambient dart connectivity makes that set
everything, which is absurd because the exterior face is never selected.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

/-- Two selected faces are dual-adjacent when one edge carries them on its two
sides. -/
def DualAdjacency {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face)
    (f g : Delta.toCombMap.Face) : Prop :=
  f ∈ faces ∧ g ∈ faces ∧
    ∃ d : Delta.toCombMap.Dart,
      Delta.toCombMap.faceOf d = f ∧
        Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = g

/-- Faces which are selected and dual-connected to a given face. -/
def DualComponent {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face)
    (f g : Delta.toCombMap.Face) : Prop :=
  g ∈ faces ∧ Relation.EqvGen (DualAdjacency Delta faces) f g

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqDualReach :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

/-! ## Vertex rotation and the face across an edge -/

/-- The vertex rotation of a dart is based in the face across that dart. -/
theorem faceOf_sigma (d : Delta.toCombMap.Dart) :
    Delta.toCombMap.faceOf (Delta.toCombMap.sigma d) =
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) := by
  have hface := Delta.toCombMap.faceOf_facePerm (Delta.toCombMap.alpha d)
  change Delta.toCombMap.faceOf
      (Delta.toCombMap.sigma (Delta.toCombMap.alpha
        (Delta.toCombMap.alpha d))) = _ at hface
  rw [Delta.toCombMap.alpha_involutive] at hface
  exact hface

/-! ## Every selected face reaches the boundary through the dual -/

/-- Every selected face is dual-connected to a face carrying a boundary
dart. -/
theorem exists_boundaryDart_dualConnected
    {faces : Finset Delta.toCombMap.Face}
    (houter : Delta.outerFace ∉ faces)
    {f : Delta.toCombMap.Face} (hf : f ∈ faces) :
    ∃ q, IsBoundaryDart Delta faces q ∧
      Relation.EqvGen (DualAdjacency Delta faces) f
        (Delta.toCombMap.faceOf q) := by
  by_contra hcon
  push Not at hcon
  have halpha : ∀ x : Delta.toCombMap.Dart,
      DualComponent Delta faces f (Delta.toCombMap.faceOf x) →
        DualComponent Delta faces f
          (Delta.toCombMap.faceOf (Delta.toCombMap.alpha x)) := by
    intro x hx
    have hmem : Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) ∈ faces := by
      by_contra hno
      exact hcon x ⟨hx.1, hno⟩ hx.2
    refine ⟨hmem, ?_⟩
    refine Relation.EqvGen.trans _ _ _ hx.2 ?_
    exact Relation.EqvGen.rel _ _ ⟨hx.1, hmem, x, rfl, rfl⟩
  have halphaRev : ∀ x : Delta.toCombMap.Dart,
      DualComponent Delta faces f
          (Delta.toCombMap.faceOf (Delta.toCombMap.alpha x)) →
        DualComponent Delta faces f (Delta.toCombMap.faceOf x) := by
    intro x hx
    have h := halpha (Delta.toCombMap.alpha x) hx
    rw [Delta.toCombMap.alpha_involutive] at h
    exact h
  have hsigma : ∀ x : Delta.toCombMap.Dart,
      DualComponent Delta faces f (Delta.toCombMap.faceOf x) →
        DualComponent Delta faces f
          (Delta.toCombMap.faceOf (Delta.toCombMap.sigma x)) := by
    intro x hx
    rw [faceOf_sigma]
    exact halpha x hx
  have hsigmaRev : ∀ x : Delta.toCombMap.Dart,
      DualComponent Delta faces f
          (Delta.toCombMap.faceOf (Delta.toCombMap.sigma x)) →
        DualComponent Delta faces f (Delta.toCombMap.faceOf x) := by
    intro x hx
    rw [faceOf_sigma] at hx
    exact halphaRev x hx
  have hiff : ∀ x y : Delta.toCombMap.Dart,
      Relation.EqvGen Delta.toCombMap.Adjacent x y →
        (DualComponent Delta faces f (Delta.toCombMap.faceOf x) ↔
          DualComponent Delta faces f (Delta.toCombMap.faceOf y)) := by
    intro x y hxy
    induction hxy with
    | rel a b hab =>
        rcases hab with hab | hab
        · subst hab
          exact ⟨halpha a, halphaRev a⟩
        · subst hab
          exact ⟨hsigma a, hsigmaRev a⟩
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ihab ihbc => exact ihab.trans ihbc
  have hsource : Delta.toCombMap.faceOf
      ((Delta.faceBoundary f).darts.head (Delta.faceBoundary f).nonempty) = f :=
    ((Delta.faceBoundary f).mem_iff _).mp
      (List.head_mem (Delta.faceBoundary f).nonempty)
  have hexterior : Delta.toCombMap.faceOf
      ((Delta.faceBoundary Delta.outerFace).darts.head
        (Delta.faceBoundary Delta.outerFace).nonempty) = Delta.outerFace :=
    ((Delta.faceBoundary Delta.outerFace).mem_iff _).mp
      (List.head_mem (Delta.faceBoundary Delta.outerFace).nonempty)
  have hTsource : DualComponent Delta faces f
      (Delta.toCombMap.faceOf
        ((Delta.faceBoundary f).darts.head (Delta.faceBoundary f).nonempty)) := by
    rw [hsource]
    exact ⟨hf, Relation.EqvGen.refl _⟩
  have hpath := Delta.planar.1
    ((Delta.faceBoundary f).darts.head (Delta.faceBoundary f).nonempty)
    ((Delta.faceBoundary Delta.outerFace).darts.head
      (Delta.faceBoundary Delta.outerFace).nonempty)
  have hTexterior := (hiff _ _ hpath).mp hTsource
  rw [hexterior] at hTexterior
  exact houter hTexterior.1

/-! ## The dual along the boundary cycle -/

private theorem dualAdjacency_of_internalMove
    {faces : Finset Delta.toCombMap.Face}
    {d e : Delta.toCombMap.Dart}
    (hmove : InternalBoundaryMove Delta faces d e) :
    DualAdjacency Delta faces
      (Delta.toCombMap.faceOf d) (Delta.toCombMap.faceOf e) := by
  rcases hmove with ⟨hd, hda, rfl⟩
  refine ⟨hd, ?_, ?_⟩
  · rw [Delta.toCombMap.faceOf_facePerm]
    exact hda
  refine ⟨d, rfl, ?_⟩
  exact (Delta.toCombMap.faceOf_facePerm (Delta.toCombMap.alpha d)).symm

private theorem dualEqvGen_of_boundaryStep
    {faces : Finset Delta.toCombMap.Face}
    {d e : Delta.toCombMap.Dart}
    (hstep : BoundaryStep Delta faces d e) :
    Relation.EqvGen (DualAdjacency Delta faces)
      (Delta.toCombMap.faceOf d) (Delta.toCombMap.faceOf e) := by
  have hlift : Relation.ReflTransGen
      (DualAdjacency Delta faces)
      (Delta.toCombMap.faceOf (Delta.toCombMap.facePerm d))
      (Delta.toCombMap.faceOf e) := by
    apply hstep.2.2.lift (fun x => Delta.toCombMap.faceOf x)
    intro a b hab
    exact dualAdjacency_of_internalMove hab
  have hstart : Delta.toCombMap.faceOf
      (Delta.toCombMap.facePerm d) = Delta.toCombMap.faceOf d :=
    Delta.toCombMap.faceOf_facePerm d
  rw [hstart] at hlift
  exact Relation.EqvGen.reflTransGen_le_eqvGen _ hlift

private theorem dualEqvGen_head_to_mem
    {faces : Finset Delta.toCombMap.Face}
    {cycle : List Delta.toCombMap.Dart}
    (hne : cycle ≠ [])
    (hchain : cycle.IsChain (BoundaryStep Delta faces))
    {d : Delta.toCombMap.Dart} (hd : d ∈ cycle) :
    Relation.EqvGen (DualAdjacency Delta faces)
      (Delta.toCombMap.faceOf (cycle.head hne))
      (Delta.toCombMap.faceOf d) := by
  induction cycle with
  | nil => exact (hne rfl).elim
  | cons a tail ih =>
      by_cases hda : d = a
      · subst d
        exact Relation.EqvGen.refl _
      · have hdtail : d ∈ tail := by
          rcases List.mem_cons.mp hd with had | htail
          · exact (hda had).elim
          · exact htail
        cases tail with
        | nil => simp at hdtail
        | cons b tail =>
            have hab : BoundaryStep Delta faces a b :=
              (List.isChain_cons_cons.mp hchain).1
            have htail : List.IsChain (BoundaryStep Delta faces) (b :: tail) :=
              hchain.tail
            have hhead : Relation.EqvGen (DualAdjacency Delta faces)
                (Delta.toCombMap.faceOf b) (Delta.toCombMap.faceOf d) :=
              ih (by simp) htail hdtail
            exact Relation.EqvGen.trans _ _ _
              (dualEqvGen_of_boundaryStep hab) hhead

/-- Any two faces occurring on the boundary cycle are dual-connected. -/
theorem boundaryCycle_dual_connected
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    {d e : Delta.toCombMap.Dart}
    (hd : d ∈ boundary.cycle) (he : e ∈ boundary.cycle) :
    Relation.EqvGen (DualAdjacency Delta faces)
      (Delta.toCombMap.faceOf d) (Delta.toCombMap.faceOf e) := by
  have hhead_d := dualEqvGen_head_to_mem boundary.cycle_nonempty
    boundary.cycle_chain hd
  have hhead_e := dualEqvGen_head_to_mem boundary.cycle_nonempty
    boundary.cycle_chain he
  exact Relation.EqvGen.trans _ _ _ hhead_d.symm hhead_e

/-- The selected-face dual is connected on the whole selected carrier.  This is
the statement `selectedFaces_connected` was meant to provide. -/
theorem dualFaces_connected
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    {f g : Delta.toCombMap.Face} (hf : f ∈ faces) (hg : g ∈ faces) :
    Relation.EqvGen (DualAdjacency Delta faces) f g := by
  have houter : Delta.outerFace ∉ faces := by
    intro hmem
    exact (boundary.all_gCells Delta.outerFace hmem).1 rfl
  obtain ⟨qf, hqf, hqfconn⟩ := exists_boundaryDart_dualConnected houter hf
  obtain ⟨qg, hqg, hqgconn⟩ := exists_boundaryDart_dualConnected houter hg
  have hcf : qf ∈ boundary.cycle := (boundary.cycle_mem_iff qf).2 hqf
  have hcg : qg ∈ boundary.cycle := (boundary.cycle_mem_iff qg).2 hqg
  exact Relation.EqvGen.trans _ _ _ hqfconn
    (Relation.EqvGen.trans _ _ _
      (boundaryCycle_dual_connected boundary hcf hcg) hqgconn.symm)

end Embedded
end VanKampen
end GGT
end GroupApproximation
