import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Def
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.InitialClass
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, lane gl-p06-06: lake freeness when the outer cycle follows the boundary

Lane gl-p06-06 of `carto-gl-p06`.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` […];
> (ii) `Γ_1` contains all `Γ_{i,1}`'s."

This is the **corrected, true** form of the lane's `SideOutsideReachStatement`
(`InitialStatement.lean`), which is false: see there for the pinched-annulus counterexample.  The
outer Euler equality is replaced by the hypothesis that the outer boundary cycle
`w.reverse.map α` of a noncrossing walk `w` *follows the boundary* of `sideOutside M w`.

## Truth check and proof

Write `R` for `CombMap.FaceClassStep M (walkKeep M w)`.

* `eqvGen_of_followsBoundary`: any two darts on faces off `sideFaces M w` are `R`-equivalent.
  Each of them is `R`-equivalent to a dart `y` with `α y ∈ w`
  (`exists_alpha_mem_of_not_mem_sideFaces`, using connectivity), which is a dart of the outer
  cycle (`isBoundaryDart_sideOutside_iff`), and all darts of the outer cycle are `R`-equivalent
  (`eqvGen_of_mem_cycle`, using `FollowsBoundary` and that internal edges of `sideOutside` are off
  the walk).
* `mem_component_of_followsBoundary`: the step `R` crosses only edges off the walk, and an edge of
  the boundary of `sideFaces M w` is a walk edge (`isBoundaryDart_sideFaces_iff`), so `R`-paths are
  reaches for `ExteriorComponent.component M (sideFaces M w)` (`faceClass_mono`).
* Endpoints: `sideOutsideReachFollows` (the corrected statement, proved) and
  `lakeFree_toCellPocketFaceSetOfNoncrossing_of_followsBoundary`.

The pinched annulus satisfies both Euler equalities but not `FollowsBoundary`: from the dart of
the exterior face at the pinch vertex, the old face rotation stays on the exterior face instead of
passing through internal darts to the inner circle.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.7(b)); certifies no printed sentence.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial

universe u w v

open Embedded HullSC WordMetric Surgery.MapCollapse SimpleClosedWalkSides

section Map

variable {M : CombMap.{v}} {wk : List M.Dart}

/-- Every face is the face of a dart. -/
theorem exists_faceOf_eq (f : M.Face) : ∃ x, M.faceOf x = f :=
  Quotient.inductionOn' f fun x => ⟨x, rfl⟩

/-- **Darts off the side of a noncrossing walk form one face class** when the outer cycle follows
the boundary. -/
theorem eqvGen_of_followsBoundary (hw : IsNoncrossingClosedWalk M wk) (hM : M.IsPlanar)
    (hfollow : (hw.outerCycle hM).FollowsBoundary) {x y : M.Dart}
    (hx : M.faceOf x ∉ sideFaces M wk) (hy : M.faceOf y ∉ sideFaces M wk) :
    Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M wk)) x y := by
  have hconn := CombMap.connected_of_planar M hM
  obtain ⟨a, ha, hxa⟩ := exists_alpha_mem_of_not_mem_sideFaces hconn hw.ne_nil hx
  obtain ⟨b, hb, hyb⟩ := exists_alpha_mem_of_not_mem_sideFaces hconn hw.ne_nil hy
  have ha' : a ∈ (hw.outerCycle hM).cycle :=
    ((hw.outerCycle hM).cycle_mem_iff a).mpr ((hw.isBoundaryDart_sideOutside_iff hM a).mpr ha)
  have hb' : b ∈ (hw.outerCycle hM).cycle :=
    ((hw.outerCycle hM).cycle_mem_iff b).mpr ((hw.isBoundaryDart_sideOutside_iff hM b).mpr hb)
  have hab : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M wk)) a b :=
    eqvGen_of_mem_cycle (fun z hz => not_walkKeep_of_internalDart hz) hfollow ha' hb'
  exact Relation.EqvGen.trans _ _ _ hxa
    (Relation.EqvGen.trans _ _ _ hab (Relation.EqvGen.symm _ _ hyb))

/-- **Every face off the side of a noncrossing walk is in the piece of every other one**, when the
outer cycle follows the boundary. -/
theorem mem_component_of_followsBoundary (hw : IsNoncrossingClosedWalk M wk) (hM : M.IsPlanar)
    (hfollow : (hw.outerCycle hM).FollowsBoundary) {o f : M.Face}
    (ho : o ∉ sideFaces M wk) (hf : f ∉ sideFaces M wk) :
    f ∈ ExteriorComponent.component M (sideFaces M wk) o := by
  obtain ⟨x, rfl⟩ := exists_faceOf_eq o
  obtain ⟨y, rfl⟩ := exists_faceOf_eq f
  refine ExteriorComponent.mem_component_iff.mpr ⟨y, rfl, x, rfl, ?_⟩
  refine faceClass_mono M (fun z hz hbe => hz ?_) (eqvGen_of_followsBoundary hw hM hfollow ho hf)
  rcases hbe with hbd | hbd
  · exact Or.inl ((hw.isBoundaryDart_sideFaces_iff hM z).mp hbd)
  · exact Or.inr ((hw.isBoundaryDart_sideFaces_iff hM (M.alpha z)).mp hbd)

end Map

/-- **The corrected reach statement** (true, proved below as `sideOutsideReachFollows`): for a
noncrossing walk whose outer cycle follows the boundary of `sideOutside`, with the exterior face
off its side, every face of `sideOutside` lies in the exterior piece of `sideFaces`.  It replaces
the outer Euler equality of the false `SideOutsideReachStatement` by `FollowsBoundary`. -/
def SideOutsideReachFollowsStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (X : DiscDiagram.{u, w, v} W) (walk : List X.toCombMap.Dart)
    (hw : IsNoncrossingClosedWalk X.toCombMap walk),
    X.outerFace ∉ sideFaces X.toCombMap walk →
    (hw.outerCycle X.planar).FollowsBoundary →
    ∀ f ∈ sideOutside X.toCombMap walk,
      f ∈ ExteriorComponent.component X.toCombMap (sideFaces X.toCombMap walk) X.outerFace

/-- **The corrected reach statement holds.** -/
theorem sideOutsideReachFollows : SideOutsideReachFollowsStatement.{u, w, v} := by
  intro G _ Lambda W X walk hw hout hfollow f hf
  exact mem_component_of_followsBoundary hw X.planar hfollow hout
    ((mem_sideOutside_iff X.toCombMap walk f).mp hf)

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The cell pocket face set of a noncrossing walk is lake free** when the outer cycle of the
walk follows the boundary of the walk's outside. -/
theorem lakeFree_toCellPocketFaceSetOfNoncrossing_of_followsBoundary
    (K : CellPocketWalk D eps X i j) (kept : Fin X.rCellCount)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hoff : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hkept : (cell X kept).face ∈ sideFaces X.toCombMap K.walk)
    (hfollow : (hw.outerCycle X.planar).FollowsBoundary) :
    CellPocketLakeFree (K.toCellPocketFaceSetOfNoncrossing kept hw hoff hkept) := by
  intro f hf
  exact mem_component_of_followsBoundary hw X.planar hfollow hoff hf

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.exists_faceOf_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.eqvGen_of_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.mem_component_of_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.SideOutsideReachFollowsStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.sideOutsideReachFollows
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.lakeFree_toCellPocketFaceSetOfNoncrossing_of_followsBoundary
