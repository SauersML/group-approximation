import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDef
import GroupApproximation.GGT.VanKampen.FaceSetCircuitNoncrossing
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-70: boundary darts of a lobe-closed face set

Write `Q₀ = PocketClass.pocketKeep a b K` for the edges of `K.walk`, `∂a` and `∂b`, and
`P₀ = FourPieceWitness.keepClass a b K c` for the `Q₀`-class of `c`.  Let `F ⊇ P₀` be a face set
whose other faces leave `F` only across `G₁`/`G₂` edges ("lobes behind `G`-loops").

* `pinchCut_dart_of_lobe`: every boundary dart `e` of `F` satisfies the dart predicate of branch 1
  of the target: `e ∈ invDarts G₁`, `e ∈ invDarts G₂`, or `e` is a `Q₀` dart based on the side of
  `K.walk`, off `a` and `b`.  The reason is that a boundary dart of `P₀` is a `Q₀` dart, since
  otherwise the class of `c` crosses it.
* `pinchCut_mem_sideFaces_of_boundary`: a nonempty walk made of boundary darts of `P₀` has `c` on
  its side.  Its edges are `Q₀` edges, so the `Q₀`-class of `c` refines its side classes.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- A face of the `Q₀`-class of `c` lies in the pocket class of `c`. -/
theorem pinchCut_mem_pocketClass {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c f : X.toCombMap.Face}
    (hf : f ∈ FourPieceWitness.keepClass a b K c) : f ∈ PocketClass.pocketClass a b K c :=
  PocketClass.mem_pocketClass_iff.mpr
    ((PocketNoncrossing.mem_faceClass_iff X.toCombMap (PocketClass.pocketKeep a b K) c f).mp hf)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_mem_pocketClass

/-- `Q₀` is closed under reversing a dart. -/
theorem pinchCut_pocketKeep_alpha (a b : RegionCandidate D eps X)
    (K : CellPocketWalk D eps X i j) (d : X.toCombMap.Dart) :
    PocketClass.pocketKeep a b K (X.toCombMap.alpha d) ↔ PocketClass.pocketKeep a b K d := by
  simp only [PocketClass.pocketKeep, SimpleClosedWalkSides.walkKeep_alpha]

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_pocketKeep_alpha

/-- A boundary dart of the `Q₀`-class of `c` is a `Q₀` dart. -/
theorem pinchCut_pocketKeep_of_isBoundaryDart {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face} {e : X.toCombMap.Dart}
    (he : Surgery.MapCollapse.IsBoundaryDart X.toCombMap
      (FourPieceWitness.keepClass a b K c) e) :
    PocketClass.pocketKeep a b K e := by
  by_contra hk
  exact he.2 (PocketNoncrossing.faceOf_alpha_mem_faceClass X.toCombMap
    (PocketClass.pocketKeep a b K) c hk he.1)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_pocketKeep_of_isBoundaryDart

/-- The darts of a boundary circuit of a face set are boundary darts of it. -/
theorem pinchCut_isBoundaryDart_of_mem {M : CombMap.{v}} {faces : Finset M.Face}
    {comp : FaceSetCircuits.Component M faces} {d : M.Dart}
    (hd : d ∈ FaceSetCircuits.circuit M faces comp) :
    Surgery.MapCollapse.IsBoundaryDart M faces d :=
  ((FaceSetCircuits.mem_circuit_iff M faces comp d).mp hd).elim fun h _ => h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_isBoundaryDart_of_mem

/-- An edge of a walk of boundary darts of the `Q₀`-class of `c` is a `Q₀` edge. -/
theorem pinchCut_pocketKeep_of_walkKeep {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face} {w' : List X.toCombMap.Dart}
    (hbd : ∀ d ∈ w', Surgery.MapCollapse.IsBoundaryDart X.toCombMap
      (FourPieceWitness.keepClass a b K c) d)
    {x : X.toCombMap.Dart} (hx : walkKeep X.toCombMap w' x) :
    PocketClass.pocketKeep a b K x := by
  rcases (show x ∈ w' ∨ X.toCombMap.alpha x ∈ w' from hx) with h | h
  · exact pinchCut_pocketKeep_of_isBoundaryDart (hbd x h)
  · exact (pinchCut_pocketKeep_alpha a b K x).mp
      (pinchCut_pocketKeep_of_isBoundaryDart (hbd _ h))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_pocketKeep_of_walkKeep

/-- **`c` lies on the side of a nonempty walk of boundary darts of its `Q₀`-class.** -/
theorem pinchCut_mem_sideFaces_of_boundary {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face} {w' : List X.toCombMap.Dart}
    (hne : w' ≠ [])
    (hbd : ∀ d ∈ w', Surgery.MapCollapse.IsBoundaryDart X.toCombMap
      (FourPieceWitness.keepClass a b K c) d) :
    c ∈ sideFaces X.toCombMap w' := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil w' hne
  obtain ⟨y, hy, hye⟩ := (PocketNoncrossing.faceOf_mem_faceClass_iff X.toCombMap
    (PocketClass.pocketKeep a b K) c e).mp (hbd e he).1
  have hkk : ∀ x, ¬ PocketClass.pocketKeep a b K x → ¬ walkKeep X.toCombMap w' x :=
    fun x hx hk => hx (pinchCut_pocketKeep_of_walkKeep hbd hk)
  have hs := (mem_sideFaces_iff X.toCombMap w' y).mpr
    ⟨e, he, Relation.EqvGen.symm _ _ (SimpleClosedWalkSides.faceClass_mono X.toCombMap hkk hye)⟩
  rw [hy] at hs
  exact hs

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_mem_sideFaces_of_boundary

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
