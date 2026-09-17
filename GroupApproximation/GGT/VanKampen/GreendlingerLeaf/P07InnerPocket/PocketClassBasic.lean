import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the pocket face class, basic avoidance

Lane `gl-p07-03` of the route 3 cartography (`lanes/carto-gl-p07.md`), first module.  This is
infrastructure for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`P07LakeExclusion/InnerTwoArcLong.lean`), from Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).  It certifies no printed sentence on its own.

## Notation

* `M = X.toCombMap`.
* `pocketKeep a b K` is `Q₀ = walkKeep K.walk ∨ walkKeep ∂a ∨ walkKeep ∂b`.
* `pocketClass a b K c` is the set of faces reached from darts of `c` along
  `EqvGen (FaceClassStep M Q₀)`.

## Proof route

1. `iff_of_faceClass` is a local copy of the invariance of a predicate along a face class.  A
   predicate that is invariant under face moves and under crossings of unkept edges is constant
   along the class.
2. `faceOf_mem_iff_of_faceClass`: let `B` be a boundary cycle of a face set `F` whose edges are
   kept.  Then "the face is in `F`" is constant along the class.  An unkept crossing uses an edge
   off `B.cycle`, and neither of its darts is a boundary dart of `F`.
3. `not_mem_left_of_mem_pocketClass` and `not_mem_right_of_mem_pocketClass` are step 2 for the
   boundaries of `a` and `b`.
4. `mem_sideFaces_of_mem_pocketClass`: `walkKeep K.walk ⊆ Q₀`.  So a `Q₀` class is contained in a
   `walkKeep K.walk` class (`faceClass_mono`), and `mem_sideFaces_iff` concludes.
5. `pocketClass_ne_outerFace` follows from 4 and `o ∉ sideFaces K.walk`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

namespace PocketClass

/-- A predicate invariant under face moves and under the allowed crossings is constant along a
face class. -/
theorem iff_of_faceClass {M : CombMap.{v}} (Q : M.Dart → Prop) {keep : M.Dart → Prop}
    (hface : ∀ x, Q (M.facePerm x) ↔ Q x) (halpha : ∀ x, ¬ keep x → (Q (M.alpha x) ↔ Q x))
    {x y : M.Dart} (h : Relation.EqvGen (CombMap.FaceClassStep M keep) x y) : Q x ↔ Q y := by
  induction h with
  | rel a b hab =>
      rcases hab with rfl | ⟨hk, rfl⟩
      · exact (hface a).symm
      · exact (halpha a hk).symm
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.iff_of_faceClass

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}

/-- Membership in a face set is constant along a face class whose kept darts include the edges
of a boundary cycle of that face set. -/
theorem faceOf_mem_iff_of_faceClass {faces : Finset X.toCombMap.Face}
    (B : FaceSetBoundary X faces) {keep : X.toCombMap.Dart → Prop}
    (hkeep : ∀ z, walkKeep X.toCombMap B.cycle z → keep z) {x y : X.toCombMap.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap keep) x y) :
    X.toCombMap.faceOf x ∈ faces ↔ X.toCombMap.faceOf y ∈ faces := by
  refine iff_of_faceClass (M := X.toCombMap) (fun z => X.toCombMap.faceOf z ∈ faces) ?_ ?_ h
  · intro z
    show X.toCombMap.faceOf (X.toCombMap.facePerm z) ∈ faces ↔ X.toCombMap.faceOf z ∈ faces
    rw [X.toCombMap.faceOf_facePerm z]
  · intro z hz
    have hz' : ¬ walkKeep X.toCombMap B.cycle z := fun hk => hz (hkeep z hk)
    show X.toCombMap.faceOf (X.toCombMap.alpha z) ∈ faces ↔ X.toCombMap.faceOf z ∈ faces
    constructor
    · intro hα
      by_contra hno
      have hno' : X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha z)) ∉ faces := by
        rw [X.toCombMap.alpha_involutive z]
        exact hno
      exact hz' (Or.inr ((B.cycle_mem_iff (X.toCombMap.alpha z)).mpr (And.intro hα hno')))
    · intro hzf
      by_contra hno
      exact hz' (Or.inl ((B.cycle_mem_iff z).mpr (And.intro hzf hno)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.faceOf_mem_iff_of_faceClass

variable {i j : Fin X.rCellCount}

/-- **The pocket keep-set** `Q₀`: the edges of the pocket walk and of the two region cycles. -/
def pocketKeep (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (d : X.toCombMap.Dart) : Prop :=
  walkKeep X.toCombMap K.walk d ∨ walkKeep X.toCombMap a.2.boundary.cycle d ∨
    walkKeep X.toCombMap b.2.boundary.cycle d

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.pocketKeep

/-- **The pocket class** `cls c` of a face `c` for the keep-set `Q₀`. -/
def pocketClass (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (c : X.toCombMap.Face) : Set X.toCombMap.Face :=
  {f | ∃ x, X.toCombMap.faceOf x = f ∧ ∃ y, X.toCombMap.faceOf y = c ∧
    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (pocketKeep a b K)) y x}

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.pocketClass

theorem mem_pocketClass_iff {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {c f : X.toCombMap.Face} :
    f ∈ pocketClass a b K c ↔ ∃ x, X.toCombMap.faceOf x = f ∧ ∃ y, X.toCombMap.faceOf y = c ∧
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (pocketKeep a b K)) y x :=
  Iff.rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.mem_pocketClass_iff

/-- The class of a face outside `a` avoids `a`. -/
theorem not_mem_left_of_mem_pocketClass {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c f : X.toCombMap.Face} (hc : c ∉ a.1)
    (hf : f ∈ pocketClass a b K c) : f ∉ a.1 := by
  obtain ⟨x, rfl, y, rfl, h⟩ := mem_pocketClass_iff.mp hf
  intro hx
  exact hc ((faceOf_mem_iff_of_faceClass a.2.boundary (keep := pocketKeep a b K)
    (fun z hz => Or.inr (Or.inl hz)) h).mpr hx)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.not_mem_left_of_mem_pocketClass

/-- The class of a face outside `b` avoids `b`. -/
theorem not_mem_right_of_mem_pocketClass {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c f : X.toCombMap.Face} (hc : c ∉ b.1)
    (hf : f ∈ pocketClass a b K c) : f ∉ b.1 := by
  obtain ⟨x, rfl, y, rfl, h⟩ := mem_pocketClass_iff.mp hf
  intro hx
  exact hc ((faceOf_mem_iff_of_faceClass b.2.boundary (keep := pocketKeep a b K)
    (fun z hz => Or.inr (Or.inr hz)) h).mpr hx)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.not_mem_right_of_mem_pocketClass

/-- A `Q₀` face-class chain is a `walkKeep K.walk` face-class chain. -/
theorem faceClass_walk_of_pocket {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {x y : X.toCombMap.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (pocketKeep a b K)) y x) :
    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.walk)) y x :=
  faceClass_mono X.toCombMap (keep := pocketKeep a b K) (keep' := walkKeep X.toCombMap K.walk)
    (fun _ hz hk => hz (Or.inl hk)) h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.faceClass_walk_of_pocket

/-- The class of a side face of `K.walk` lies on that side. -/
theorem mem_sideFaces_of_mem_pocketClass {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c f : X.toCombMap.Face}
    (hc : c ∈ sideFaces X.toCombMap K.walk) (hf : f ∈ pocketClass a b K c) :
    f ∈ sideFaces X.toCombMap K.walk := by
  obtain ⟨x, rfl, y, rfl, h⟩ := mem_pocketClass_iff.mp hf
  obtain ⟨d, hd, hdy⟩ := (mem_sideFaces_iff X.toCombMap K.walk y).mp hc
  exact (mem_sideFaces_iff X.toCombMap K.walk x).mpr
    ⟨d, hd, Relation.EqvGen.trans _ _ _ hdy (faceClass_walk_of_pocket h)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.mem_sideFaces_of_mem_pocketClass

/-- The class of a side face of `K.walk` misses the outer face when the outer face is off that
side. -/
theorem pocketClass_ne_outerFace {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c f : X.toCombMap.Face}
    (hoff : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hc : c ∈ sideFaces X.toCombMap K.walk) (hf : f ∈ pocketClass a b K c) :
    f ≠ X.outerFace := by
  intro h
  have hs := mem_sideFaces_of_mem_pocketClass hc hf
  rw [h] at hs
  exact hoff hs

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClass.pocketClass_ne_outerFace

end PocketClass

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
