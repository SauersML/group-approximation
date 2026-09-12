import GroupApproximation.GGT.KazhdanHypGirthEightPrimitiveAssembly
import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.Meta.AxiomGuard

/-!
# The boundary spur, and what it kills

`KazhdanHypGirthEightVKInterface.lean`'s `LocalDiagramProjections` docstring
says that the projections are conditioned on `TriangularDiagramLocalData`
rather than on `DiscDiagram.Reduced` in order to exclude "the one-edge
boundary-spur countermodel".  This module builds that countermodel and draws
the consequence the docstring leaves implicit.

## The map

`spurCombMap` has two darts, `alpha` the swap and `sigma` the identity: one
edge, two vertices of degree one, one face.  It is connected and has Euler
characteristic `2 - 1 + 1 = 2`, so it is planar, and it carries a
`DiscDiagram` over any relator set at all, because its only face is the outer
face and it has no relator cells.  Its boundary word is a single edge
traversed in both directions.

## The consequence

`TriangularDiagramLocalData` demands `2 ≤ vertexDegree v` at every vertex of
the outer-face traversal.  Both vertices of the spur are on that traversal and
both have degree one, so

* `isEmpty_localData` — no local data exists for the spur diagram, and
* `isEmpty_constructionInputs` — `GirthEightPrimitiveAssembly.ConstructionInputs`
  is **uninhabited**, because its `localData` field asks for local data at
  every reduced diagram.

`ConstructionInputs.toPrimitives` is therefore an implication with an
impossible hypothesis: the assembly route to `GirthEightDiagramPrimitives`
cannot be completed as the contract is currently stated.  What has to change is
the *conditioning* of the `localData` field — it must be asked only of the
diagrams the geometry actually produces (spur-free fillings), not of every
reduced diagram.  Nothing below says the girth-eight programme is wrong; it
says one hypothesis of one intermediate record is too strong to be inhabited.

The three fields of `GirthEightDiagramPrimitives` that are already constructed
in the tree — `localProjection`, `cornerCycle`, `facePositions` — are
untouched by this, and so is `removeBaseCells`, whose own obligation is
satisfied vacuously by the spur (it has no inner faces at all).
-/

namespace GroupApproximation
namespace GGT
namespace GirthEightSpur

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface
open VanKampen

/-! ### The one-edge map -/

/-- Reversal of the single edge. -/
def spurAlpha : Equiv.Perm Bool := Equiv.swap true false

@[simp] theorem spurAlpha_true : spurAlpha true = false := Equiv.swap_apply_left _ _

@[simp] theorem spurAlpha_false : spurAlpha false = true := Equiv.swap_apply_right _ _

/-- The single-edge combinatorial map: two darts, no rotation. -/
def spurCombMap : CombMap.{0} where
  Dart := Bool
  dartFintype := inferInstance
  alpha := spurAlpha
  sigma := 1
  alpha_involutive := fun d ↦ by
    cases d <;> simp
  alpha_fixedPointFree := fun d ↦ by
    cases d <;> simp

@[simp] theorem spur_dart_eq : spurCombMap.Dart = Bool := rfl

@[simp] theorem spur_sigma : spurCombMap.sigma = 1 := rfl

@[simp] theorem spur_alpha : spurCombMap.alpha = spurAlpha := rfl

/-- The face rotation of the spur is the edge reversal. -/
theorem spur_facePerm : spurCombMap.facePerm = spurAlpha := by
  show spurCombMap.sigma * spurCombMap.alpha = spurAlpha
  rw [spur_sigma, spur_alpha, one_mul]

/-! ### Vertices, edges and faces -/

/-- With trivial rotation, two darts share a vertex only if they are equal. -/
theorem spur_sameCycle_sigma (d e : Bool) :
    spurCombMap.sigma.SameCycle d e ↔ d = e := by
  constructor
  · rintro ⟨i, hi⟩
    rw [spur_sigma, one_zpow] at hi
    exact hi
  · rintro rfl
    exact ⟨0, by simp⟩

theorem spur_vertexOf_injective : Function.Injective spurCombMap.vertexOf := by
  intro d e h
  rw [CombMap.vertexOf_eq_iff] at h
  exact (spur_sameCycle_sigma d e).1 h

theorem spur_vertexOf_surjective : Function.Surjective spurCombMap.vertexOf :=
  Quotient.mk''_surjective

theorem spur_vertexCount : spurCombMap.vertexCount = 2 := by
  have hbij : Function.Bijective spurCombMap.vertexOf :=
    ⟨spur_vertexOf_injective, spur_vertexOf_surjective⟩
  have h := Nat.card_congr (Equiv.ofBijective _ hbij)
  simpa [CombMap.vertexCount] using h.symm

/-- Both darts lie on the single face. -/
theorem spur_faceOf_eq (d e : Bool) : spurCombMap.faceOf d = spurCombMap.faceOf e := by
  rw [CombMap.faceOf_eq_iff]
  rcases d with _ | _ <;> rcases e with _ | _
  · exact Equiv.Perm.SameCycle.refl _ _
  · exact ⟨1, by rw [spur_facePerm]; simp⟩
  · exact ⟨1, by rw [spur_facePerm]; simp⟩
  · exact Equiv.Perm.SameCycle.refl _ _

instance spur_face_subsingleton : Subsingleton spurCombMap.Face := by
  constructor
  intro f g
  obtain ⟨d, rfl⟩ := Quotient.mk''_surjective (s := Equiv.Perm.SameCycle.setoid
    spurCombMap.facePerm) f
  obtain ⟨e, rfl⟩ := Quotient.mk''_surjective (s := Equiv.Perm.SameCycle.setoid
    spurCombMap.facePerm) g
  exact spur_faceOf_eq d e

instance spur_face_nonempty : Nonempty spurCombMap.Face :=
  ⟨spurCombMap.faceOf true⟩

theorem spur_faceCount : spurCombMap.faceCount = 1 := by
  have : Unique spurCombMap.Face := uniqueOfSubsingleton (spurCombMap.faceOf true)
  simpa [CombMap.faceCount] using Nat.card_unique (α := spurCombMap.Face)

/-- Both darts lie on the single edge. -/
theorem spur_edgeOf_eq (d e : Bool) : spurCombMap.edgeOf d = spurCombMap.edgeOf e := by
  rw [CombMap.edgeOf_eq_iff]
  rcases d with _ | _ <;> rcases e with _ | _
  · exact Or.inl rfl
  · exact Or.inr (by simp)
  · exact Or.inr (by simp)
  · exact Or.inl rfl

instance spur_edge_subsingleton : Subsingleton spurCombMap.Edge := by
  constructor
  intro f g
  obtain ⟨d, rfl⟩ := Quotient.mk''_surjective (s := spurCombMap.edgeSetoid) f
  obtain ⟨e, rfl⟩ := Quotient.mk''_surjective (s := spurCombMap.edgeSetoid) g
  exact spur_edgeOf_eq d e

theorem spur_edgeCount : spurCombMap.edgeCount = 1 := by
  have : Nonempty spurCombMap.Edge := ⟨spurCombMap.edgeOf true⟩
  have : Unique spurCombMap.Edge := uniqueOfSubsingleton (spurCombMap.edgeOf true)
  simpa [CombMap.edgeCount] using Nat.card_unique (α := spurCombMap.Edge)

/-! ### Planarity -/

theorem spur_isConnected : spurCombMap.IsConnected := by
  intro d e
  rcases d with _ | _ <;> rcases e with _ | _
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (Or.inl (by simp))
  · exact Relation.EqvGen.rel _ _ (Or.inl (by simp))
  · exact Relation.EqvGen.refl _

theorem spur_isPlanar : spurCombMap.IsPlanar := by
  refine ⟨spur_isConnected, ?_⟩
  rw [CombMap.eulerCharacteristic, spur_vertexCount, spur_edgeCount, spur_faceCount]
  norm_num

/-! ### Vertex degrees -/

theorem spur_vertexDegree (v : spurCombMap.Vertex) :
    spurCombMap.vertexDegree v = 1 := by
  obtain ⟨d, rfl⟩ := spur_vertexOf_surjective v
  have hsub : Subsingleton {e : spurCombMap.Dart //
      (Quotient.mk'' e : spurCombMap.Vertex) = spurCombMap.vertexOf d} := by
    constructor
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact Subtype.ext (spur_vertexOf_injective (ha.trans hb.symm))
  have hne : Nonempty {e : spurCombMap.Dart //
      (Quotient.mk'' e : spurCombMap.Vertex) = spurCombMap.vertexOf d} :=
    ⟨⟨d, rfl⟩⟩
  have : Unique {e : spurCombMap.Dart //
      (Quotient.mk'' e : spurCombMap.Vertex) = spurCombMap.vertexOf d} :=
    uniqueOfSubsingleton ⟨d, rfl⟩
  simpa [CombMap.vertexDegree, CombMap.orbitDegree] using
    Nat.card_unique (α := {e : spurCombMap.Dart //
      (Quotient.mk'' e : spurCombMap.Vertex) = spurCombMap.vertexOf d})

/-! ### The spur as a disc diagram

Every label is the letter of `1`, so the boundary product is trivially the
identity; the diagram has no relator cells, so it is reduced, and its only
face is the outer face, so the inner-face condition is vacuous. -/

section Diagram

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)

/-- The trivial letter used on both darts. -/
def spurLetter : GGT.RelLetter (FreeGroup Generator) PEmpty :=
  GGT.RelLetter.base 1

theorem spurLetter_inv :
    HullSC.RelWord.inv (spurLetter (Generator := Generator)) =
      spurLetter (Generator := Generator) := by
  show GGT.RelLetter.base (1 : FreeGroup Generator)⁻¹ =
    GGT.RelLetter.base (1 : FreeGroup Generator)
  rw [inv_one]

theorem spurLetter_val :
    (spurLetter (Generator := Generator)).val = 1 := rfl

/-- The one-edge disc diagram over any relator set. -/
noncomputable def spurDiscDiagram :
    VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T) where
  toCombMap := spurCombMap
  planar := spur_isPlanar
  label := fun _ ↦ spurLetter
  label_alpha := fun _ ↦ (spurLetter_inv).symm
  outerFace := spurCombMap.faceOf true
  faceBoundary := fun f ↦
    (Subsingleton.elim (spurCombMap.faceOf true) f) ▸
      VanKampen.FaceBoundary.based spurCombMap true
  relatorCells := []
  relatorCell_faces_nodup := by simp
  relatorCell_word := by simp
  inner_face := fun f hf ↦ absurd (Subsingleton.elim f _) hf
  boundary_product := by
    simp only [List.map_nil, List.prod_nil]
    symm
    rw [GGT.RelLetter.listVal]
    refine List.prod_eq_one ?_
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [HullSC.RelWord.revInv, List.mem_reverse, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    simp only [List.mem_map] at hb
    obtain ⟨d, -, rfl⟩ := hb
    rw [spurLetter_inv]
    exact spurLetter_val

theorem spur_relatorCells : (spurDiscDiagram T).relatorCells = [] := rfl

/-- The spur diagram is reduced: it has no relator cells at all. -/
theorem spur_reduced : (spurDiscDiagram T).Reduced :=
  VanKampen.DiscDiagram.reduced_of_no_rCells _ (spur_relatorCells T)

/-- The outer traversal of the spur visits a vertex. -/
theorem spur_boundaryVertices_nonempty :
    (discOuterBoundaryVertices (spurDiscDiagram T)).Nonempty := by
  classical
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _
    ((spurDiscDiagram T).faceBoundary (spurDiscDiagram T).outerFace).nonempty
  refine ⟨(spurDiscDiagram T).toCombMap.vertexOf d, ?_⟩
  simp only [discOuterBoundaryVertices, List.mem_toFinset, List.mem_map]
  exact ⟨d, hd, rfl⟩

/-! ### The consequence -/

/-- **No local data exists for the spur diagram.**  Its outer traversal visits
a vertex of degree one, and `TriangularDiagramLocalData` demands degree at
least two at every such vertex. -/
theorem isEmpty_localData :
    IsEmpty (TriangularDiagramLocalData T (spurDiscDiagram T)) := by
  constructor
  intro L
  obtain ⟨v, hv⟩ := spur_boundaryVertices_nonempty T
  have h2 := L.boundaryVertexDegree v hv
  have h1 : (spurDiscDiagram T).toCombMap.vertexDegree v = 1 :=
    spur_vertexDegree v
  omega

/-- **The residual construction contract is uninhabited.**

`GirthEightPrimitiveAssembly.ConstructionInputs.localData` asks for local data
at *every* reduced diagram, and the spur is a reduced diagram with none.  So
`ConstructionInputs.toPrimitives` is an implication whose hypothesis cannot be
met, and the `localData` field has to be reconditioned — asked only of the
diagrams the geometry produces — before the assembly route to
`GirthEightDiagramPrimitives` can be completed. -/
theorem isEmpty_constructionInputs :
    IsEmpty (GirthEightPrimitiveAssembly.ConstructionInputs (T := T)) := by
  constructor
  intro H
  exact (isEmpty_localData T).false (H.localData (spurDiscDiagram T) (spur_reduced T))

end Diagram

end GirthEightSpur
end GGT
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.GGT.GirthEightSpur.spur_isPlanar
#audit_axioms GroupApproximation.GGT.GirthEightSpur.isEmpty_localData
#audit_axioms GroupApproximation.GGT.GirthEightSpur.isEmpty_constructionInputs
