import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClassBasic
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossingClass
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketCellOffComponent
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-21a: the cut-down witness of the reading residual

This lane sits above `PocketFourPieceInputProofResidualStatement`
(`FourPieceInputProofStatement.lean`, lane gl-p07-20b), from Osin, arXiv:math/0411039v3, §9,
proof of Lemma 9.7(b).  This module defines the witness face set.  It certifies no printed
sentence on its own.

## Notation

* `M = X.toCombMap`, `Q₀ = PocketClass.pocketKeep a b K`.
* `keepClass a b K c` is the `Q₀`-class of `c` (`PocketNoncrossing.faceClass`).
* `block a b K c` is `P = keepClass a b K c ∪ sideOutside K.walk`.
* `cut a b K c` is the union of the pieces `component M P h` of the faces `h ∈ a.1 ∪ b.1` off `P`.
  These are the faces joined to a strip of `a` or `b` without crossing an edge of `∂P`.
* `IsOpenFace f` means `f ∈ sideFaces K.walk` and `f ∉ cut`.
* `Touch f g` means that `f` and `g` share an edge or a vertex.
* `witnessFaces a b K c` is the set of open faces reached from `c` by `Touch` steps through open
  faces.

## Why this witness

* The `Q₀`-class of `C` is open: it lies in `P` and misses every piece off `P`.
* A lake of `C` is open and shares an edge with the class.
* A sub-pocket `P'` of the self-pinch model touches `C` at the pinch vertex.  It is off `P`, and
  it is not joined to `a` or `b`: its edges go to `Π_i`, which lies in `sideOutside K.walk ⊆ P`.
  So `P'` is open and reached by a vertex step.
* Every strip of `a` or `b` inside `sideFaces K.walk` is cut.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Two faces touch**: they share an edge or a vertex. -/
def Touch (M : CombMap.{v}) (f g : M.Face) : Prop :=
  (∃ d, M.faceOf d = f ∧ M.faceOf (M.alpha d) = g) ∨
    ∃ d e, M.faceOf d = f ∧ M.faceOf e = g ∧ M.vertexOf d = M.vertexOf e

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.Touch

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The `Q₀`-class of a face.** -/
noncomputable def keepClass (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (c : X.toCombMap.Face) : Finset X.toCombMap.Face :=
  PocketNoncrossing.faceClass X.toCombMap (PocketClass.pocketKeep a b K) c

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.keepClass

/-- **The blocking set** `P`: the `Q₀`-class of `c` and the outside of the pocket walk. -/
noncomputable def block (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (c : X.toCombMap.Face) : Finset X.toCombMap.Face := by
  classical
  exact Finset.univ.filter fun f => f ∈ keepClass a b K c ∨ f ∈ sideOutside X.toCombMap K.walk

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.block

/-- **The cut**: the pieces, for `P`, of the faces of `a` and `b` off `P`. -/
noncomputable def cut (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (c : X.toCombMap.Face) : Finset X.toCombMap.Face := by
  classical
  exact Finset.univ.filter fun f => ∃ h, (h ∈ a.1 ∨ h ∈ b.1) ∧ h ∉ block a b K c ∧
    f ∈ ExteriorComponent.component X.toCombMap (block a b K c) h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.cut

/-- **An open face**: on the side of the pocket walk and off the cut. -/
def IsOpenFace (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (c f : X.toCombMap.Face) : Prop :=
  f ∈ sideFaces X.toCombMap K.walk ∧ f ∉ cut a b K c

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.IsOpenFace

/-- **A step** between two open faces that touch. -/
def Step (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (c f g : X.toCombMap.Face) : Prop :=
  IsOpenFace a b K c f ∧ IsOpenFace a b K c g ∧ Touch X.toCombMap f g

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.Step

/-- **The witness face set**: the open faces reached from `c` by steps. -/
noncomputable def witnessFaces (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (c : X.toCombMap.Face) : Finset X.toCombMap.Face := by
  classical
  exact Finset.univ.filter fun f =>
    IsOpenFace a b K c f ∧ Relation.ReflTransGen (Step a b K c) c f

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessFaces

theorem mem_block_iff {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {c f : X.toCombMap.Face} :
    f ∈ block a b K c ↔ f ∈ keepClass a b K c ∨ f ∈ sideOutside X.toCombMap K.walk := by
  classical
  unfold block
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ f)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.mem_block_iff

theorem mem_cut_iff {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {c f : X.toCombMap.Face} :
    f ∈ cut a b K c ↔ ∃ h, (h ∈ a.1 ∨ h ∈ b.1) ∧ h ∉ block a b K c ∧
      f ∈ ExteriorComponent.component X.toCombMap (block a b K c) h := by
  classical
  unfold cut
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ f)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.mem_cut_iff

theorem mem_witnessFaces_iff {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {c f : X.toCombMap.Face} :
    f ∈ witnessFaces a b K c ↔
      IsOpenFace a b K c f ∧ Relation.ReflTransGen (Step a b K c) c f := by
  classical
  unfold witnessFaces
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ f)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.mem_witnessFaces_iff

/-- **Clause 1**: the witness lies on the side of the pocket walk. -/
theorem witnessFaces_subset_sideFaces {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face} :
    witnessFaces a b K c ⊆ sideFaces X.toCombMap K.walk :=
  fun _ hf => (mem_witnessFaces_iff.mp hf).1.1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessFaces_subset_sideFaces

/-- A face lies in its own `Q₀`-class. -/
theorem self_mem_keepClass (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (c : X.toCombMap.Face) : c ∈ keepClass a b K c := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep c
  exact (PocketNoncrossing.mem_faceClass_iff X.toCombMap (PocketClass.pocketKeep a b K) _ _).mpr
    ⟨x, rfl, x, rfl, Relation.EqvGen.refl x⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.self_mem_keepClass

/-- **The start face is a witness face** when it lies on the side of the pocket walk. -/
theorem mem_witnessFaces_self {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {c : X.toCombMap.Face} (hc : c ∈ sideFaces X.toCombMap K.walk) :
    c ∈ witnessFaces a b K c := by
  refine mem_witnessFaces_iff.mpr ⟨⟨hc, ?_⟩, Relation.ReflTransGen.refl⟩
  intro hcut
  obtain ⟨_, _, hh, hmem⟩ := mem_cut_iff.mp hcut
  exact ExteriorComponent.not_mem_of_mem_component hh hmem
    (mem_block_iff.mpr (Or.inl (self_mem_keepClass a b K c)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.mem_witnessFaces_self

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
