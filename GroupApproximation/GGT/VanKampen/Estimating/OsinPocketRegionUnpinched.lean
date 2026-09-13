import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFollowsBoundary
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Unpinched face sets

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A face set is unpinched when no vertex carries two of its boundary
darts, so that its boundary walk visits no vertex twice.  Then the complement's cycle is the face
set's cycle read backwards across the edges, and both cycles follow the boundary.  A walk with a
repeated vertex is a pinch.

* `Surgery.MapCollapse.Unpinched`: no vertex carries two boundary darts of the face set.
  `BoundaryCycle.unpinched_iff_nodup`: equivalently, the darts of a boundary cycle start at
  distinct vertices.
* `vertexOf_eq_of_boundaryWalk`: a boundary walk from `d` turns around the vertex of `alpha d`.
  So an unpinched cycle that follows the boundary is a simple closed walk
  (`BoundaryCycle.isSimpleClosedWalk_of_followsBoundary`), and a boundary cycle that is a simple
  closed walk is unpinched (`BoundaryCycle.unpinched_of_isSimpleClosedWalk`).
* `boundaryWalk_eq_of_isBoundaryDart`: a boundary walk stops at the first boundary dart.  So a
  boundary cycle that follows the boundary has the actual first return as successor
  (`BoundaryCycle.boundaryPerm_eq_of_followsBoundary`), and the face set has one boundary
  circuit (`BoundaryCycle.exists_component_of_followsBoundary`).
* `Unpinched.boundaryWalk_alpha`: for an unpinched face set, a boundary walk from `d` to `e` gives
  a boundary walk of the complement from `alpha e` to `alpha d`.
* `BoundaryCycle.reverseAlpha` and `BoundaryCycle.reverseAlpha_followsBoundary`: the reversed
  cycle across the edges is a boundary cycle of the complement, and it follows the boundary.
* `PocketRegion.ofUnpinched`: an unpinched disc region away from the exterior face whose cycle
  follows the boundary is a pocket region, and its complement cycle follows the boundary too.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace Surgery.MapCollapse

/-- **An unpinched face set**: no vertex carries two boundary darts of the face set, so the
boundary walk visits every vertex at most once. -/
def Unpinched (M : CombMap.{v}) (faces : Finset M.Face) : Prop :=
  ∀ x y : M.Dart, IsBoundaryDart M faces x → IsBoundaryDart M faces y →
    M.vertexOf x = M.vertexOf y → x = y

private theorem facePerm_alpha_apply (M : CombMap.{v}) (d : M.Dart) :
    M.facePerm (M.alpha d) = M.sigma d := by
  change M.sigma (M.alpha (M.alpha d)) = M.sigma d
  rw [M.alpha_involutive d]

private theorem faceOf_sigma_eq_alpha (M : CombMap.{v}) (d : M.Dart) :
    M.faceOf (M.sigma d) = M.faceOf (M.alpha d) := by
  rw [← facePerm_alpha_apply M d, M.faceOf_facePerm]

private theorem next_map_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) {l : List α} (hl : l.Nodup) {a : α} (ha : a ∈ l)
    {b : β} (hab : f a = b) (hb : b ∈ l.map f) : (l.map f).next b hb = f (l.next a ha) := by
  subst hab
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < (l.map f).length := by
    rw [List.length_map]
    exact hi
  have h := List.next_getElem (l.map f) (List.Nodup.map hf hl) i hi'
  simp only [List.getElem_map, List.length_map] at h
  rw [h, List.next_getElem l hl i hi]

variable {M : CombMap.{v}} {faces outside : Finset M.Face}

/-- **A boundary walk turns around one vertex.**  A boundary walk from `d` ends at a dart based at
the vertex of `alpha d`. -/
theorem vertexOf_eq_of_boundaryWalk {d e : M.Dart} (h : BoundaryWalk M faces d e) :
    M.vertexOf e = M.vertexOf (M.alpha d) := by
  unfold BoundaryWalk at h
  induction h with
  | refl => exact M.vertexOf_sigma (M.alpha d)
  | tail _ hstep ih => rw [← hstep.2, M.vertexOf_sigma, ih]

/-- **A boundary walk stops at the first boundary dart.**  The walk turns only through internal
darts, and a boundary dart is not internal. -/
theorem boundaryWalk_eq_of_isBoundaryDart {d e e' : M.Dart} (he : IsBoundaryDart M faces e)
    (he' : IsBoundaryDart M faces e') (h : BoundaryWalk M faces d e)
    (h' : BoundaryWalk M faces d e') : e = e' := by
  have hU : Relator.RightUnique fun x y : M.Dart => InternalDart M faces x ∧ M.sigma x = y := by
    intro _ _ _ hab hac
    exact hab.2.symm.trans hac.2
  have hstop : ∀ {a b : M.Dart}, IsBoundaryDart M faces a →
      Relation.ReflTransGen (fun x y : M.Dart => InternalDart M faces x ∧ M.sigma x = y) a b →
        a = b := by
    intro _ _ ha hab
    rcases hab.cases_head with hab | ⟨_, hac, _⟩
    · exact hab
    · exact absurd hac.1.2 ha.2
  unfold BoundaryWalk at h h'
  rcases Relation.ReflTransGen.total_of_right_unique hU h h' with h'' | h''
  · exact hstop he h''
  · exact (hstop he' h'').symm

namespace Unpinched

/-- **The complement walk.**  For an unpinched face set, a boundary walk from `d` to `e` turns
around the vertex of `alpha d`.  The darts around that vertex from `sigma e` up to `alpha d` are
based outside the face set, since the only boundary dart there is `e`; so the complement walks
from `alpha e` to `alpha d`. -/
theorem boundaryWalk_alpha (hpinch : Unpinched M faces)
    (hout : ∀ f, f ∈ outside ↔ f ∉ faces) {d e : M.Dart} (hd : IsBoundaryDart M faces d)
    (he : IsBoundaryDart M faces e) (hwalk : BoundaryWalk M faces d e) :
    BoundaryWalk M outside (M.alpha e) (M.alpha d) := by
  have key : ∀ n : ℕ, ∀ y, M.faceOf y ∉ faces → (M.sigma ^ n) (M.sigma e) = y →
      Relation.ReflTransGen (fun x y => InternalDart M outside x ∧ M.sigma x = y)
        (M.sigma e) y := by
    intro n
    induction n with
    | zero =>
      intro y _ hy
      rw [pow_zero, Equiv.Perm.one_apply] at hy
      subst hy
      exact Relation.ReflTransGen.refl
    | succ n ih =>
      intro y hyf hy
      obtain ⟨u, hu⟩ : ∃ u, (M.sigma ^ n) (M.sigma e) = u := ⟨_, rfl⟩
      have hsu : M.sigma u = y := by
        rw [← hy, pow_succ', Equiv.Perm.mul_apply, hu]
      have hau : M.faceOf (M.alpha u) ∉ faces := by
        rw [← faceOf_sigma_eq_alpha M u, hsu]
        exact hyf
      by_cases huf : M.faceOf u ∈ faces
      · have hvu : M.vertexOf u = M.vertexOf e := by
          rw [M.vertexOf_eq_iff]
          refine Equiv.Perm.SameCycle.symm (⟨((n + 1 : ℕ) : ℤ), ?_⟩ : M.sigma.SameCycle e u)
          rw [zpow_natCast, pow_succ, Equiv.Perm.mul_apply]
          exact hu
        have hue : u = e := hpinch u e ⟨huf, hau⟩ he hvu
        have hye : y = M.sigma e := by
          rw [← hsu, hue]
        subst hye
        exact Relation.ReflTransGen.refl
      · exact (ih u huf hu).tail ⟨⟨(hout _).mpr huf, (hout _).mpr hau⟩, hsu⟩
  obtain ⟨n, hn⟩ := ((M.vertexOf_eq_iff _ _).mp (vertexOf_eq_of_boundaryWalk hwalk)).exists_nat_pow_eq
  unfold BoundaryWalk
  rw [facePerm_alpha_apply M e]
  cases n with
  | zero =>
    rw [pow_zero, Equiv.Perm.one_apply] at hn
    have hmem : M.faceOf (M.alpha d) ∈ faces := by
      rw [← hn]
      exact he.1
    exact absurd hmem hd.2
  | succ m =>
    rw [pow_succ, Equiv.Perm.mul_apply] at hn
    exact key m (M.alpha d) hd.2 hn

end Unpinched

namespace BoundaryCycle

/-- A face set is unpinched exactly when the darts of a boundary cycle start at distinct
vertices. -/
theorem unpinched_iff_nodup (boundary : BoundaryCycle M faces) :
    Unpinched M faces ↔ (boundary.cycle.map M.vertexOf).Nodup := by
  constructor
  · intro h
    exact List.Nodup.map_on (fun x hx y hy hxy => h x y ((boundary.cycle_mem_iff x).mp hx)
      ((boundary.cycle_mem_iff y).mp hy) hxy) boundary.cycle_nodup
  · intro h x y hx hy hxy
    exact List.inj_on_of_nodup_map h ((boundary.cycle_mem_iff x).mpr hx)
      ((boundary.cycle_mem_iff y).mpr hy) hxy

/-- **A boundary cycle that follows the boundary has the actual successor.** -/
theorem boundaryPerm_eq_of_followsBoundary (boundary : BoundaryCycle M faces)
    (hwalk : boundary.FollowsBoundary) :
    FaceSetCircuits.boundaryPerm M faces = boundary.boundaryPerm :=
  Equiv.ext fun d => Subtype.ext (boundaryWalk_eq_of_isBoundaryDart
    (FaceSetCircuits.boundaryPerm M faces d).2 (boundary.boundaryPerm d).2
    (FaceSetCircuits.boundaryPerm_walk M faces d) (hwalk d))

/-- **One boundary circuit.**  A face set with a boundary cycle that follows the boundary has a
single circuit of the actual successor. -/
theorem exists_component_of_followsBoundary (boundary : BoundaryCycle M faces)
    (hwalk : boundary.FollowsBoundary) :
    ∃ c : FaceSetCircuits.Component M faces,
      ∀ d : BoundaryDart M faces, (Quotient.mk'' d : FaceSetCircuits.Component M faces) = c := by
  classical
  have hmem : ∀ (i : ℕ) (hi : i < boundary.cycle.length),
      IsBoundaryDart M faces boundary.cycle[i] :=
    fun _ hi => (boundary.cycle_mem_iff _).mp (List.getElem_mem hi)
  have hlen : 0 < boundary.cycle.length := List.length_pos_iff.mpr boundary.cycle_nonempty
  have key : ∀ (i : ℕ) (hi : i < boundary.cycle.length),
      boundary.boundaryPerm.SameCycle ⟨boundary.cycle[0], hmem 0 hlen⟩
        ⟨boundary.cycle[i], hmem i hi⟩ := by
    intro i
    induction i with
    | zero => exact fun _ => Equiv.Perm.SameCycle.rfl
    | succ i ih =>
      intro hi
      have hi' : i < boundary.cycle.length := Nat.lt_of_succ_lt hi
      have hval : (boundary.boundaryPerm ⟨boundary.cycle[i], hmem i hi'⟩ : M.Dart) =
          boundary.cycle[i + 1] := by
        refine (boundaryPerm_apply_val boundary _).trans
          ((List.next_getElem boundary.cycle boundary.cycle_nodup i hi').trans ?_)
        simp only [Nat.mod_eq_of_lt hi]
      have hstep : boundary.boundaryPerm ⟨boundary.cycle[i], hmem i hi'⟩ =
          ⟨boundary.cycle[i + 1], hmem (i + 1) hi⟩ :=
        Subtype.ext hval
      rw [← hstep]
      exact Equiv.Perm.sameCycle_apply_right.mpr (ih hi')
  rw [← boundaryPerm_eq_of_followsBoundary boundary hwalk] at key
  refine ⟨Quotient.mk'' ⟨boundary.cycle[0], hmem 0 hlen⟩, fun d => ?_⟩
  obtain ⟨i, hi, hd⟩ := List.getElem_of_mem ((boundary.cycle_mem_iff d.1).mpr d.2)
  obtain rfl : d = ⟨boundary.cycle[i], hmem i hi⟩ := Subtype.ext hd.symm
  exact Quotient.sound' (key i hi).symm

/-- **An unpinched cycle that follows the boundary is a simple closed walk.**  Each boundary walk
turns around the vertex of `alpha` of its first dart, so consecutive darts of the cycle meet, and
the last meets the first. -/
theorem isSimpleClosedWalk_of_followsBoundary (boundary : BoundaryCycle M faces)
    (hwalk : boundary.FollowsBoundary) (hpinch : Unpinched M faces) :
    IsSimpleClosedWalk M boundary.cycle := by
  classical
  refine ⟨boundary.cycle_nonempty, ?_, ?_, (unpinched_iff_nodup boundary).mp hpinch, ?_⟩
  · rw [List.isChain_iff_getElem]
    intro i hi
    have hi1 : i + 1 < boundary.cycle.length := by omega
    have hi0 : i < boundary.cycle.length := by omega
    have h := vertexOf_eq_of_boundaryWalk
      (hwalk ⟨boundary.cycle[i], (boundary.cycle_mem_iff _).mp (List.getElem_mem hi0)⟩)
    rw [boundaryPerm_apply_val, List.next_getElem boundary.cycle boundary.cycle_nodup i hi0] at h
    simp only [Nat.mod_eq_of_lt hi1] at h
    exact h.symm
  · have h := vertexOf_eq_of_boundaryWalk
      (hwalk ⟨boundary.cycle.getLast boundary.cycle_nonempty,
        (boundary.cycle_mem_iff _).mp (List.getLast_mem boundary.cycle_nonempty)⟩)
    rw [boundaryPerm_apply_val,
      List.next_getLast_eq_head boundary.cycle boundary.cycle_nonempty boundary.cycle_nodup] at h
    exact h.symm
  · intro d hd had
    exact ((boundary.cycle_mem_iff _).mp hd).2 ((boundary.cycle_mem_iff _).mp had).1

/-- A boundary cycle that is a simple closed walk makes the face set unpinched. -/
theorem unpinched_of_isSimpleClosedWalk (boundary : BoundaryCycle M faces)
    (hw : IsSimpleClosedWalk M boundary.cycle) : Unpinched M faces :=
  (unpinched_iff_nodup boundary).mpr hw.vertex_nodup

/-- **The complement cycle.**  Reversing a boundary cycle and crossing each edge lists the
boundary darts of the complement. -/
def reverseAlpha (boundary : BoundaryCycle M faces) (hout : ∀ f, f ∈ outside ↔ f ∉ faces) :
    BoundaryCycle M outside where
  cycle := boundary.cycle.reverse.map M.alpha
  cycle_nonempty h :=
    boundary.cycle_nonempty (List.reverse_eq_nil_iff.mp (List.map_eq_nil_iff.mp h))
  cycle_nodup :=
    List.Nodup.map M.alpha_involutive.injective (List.nodup_reverse.mpr boundary.cycle_nodup)
  cycle_mem_iff d := by
    rw [List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hb := (boundary.cycle_mem_iff a).mp (List.mem_reverse.mp ha)
      refine ⟨(hout _).mpr hb.2, ?_⟩
      rw [M.alpha_involutive a]
      exact fun h => (hout _).mp h hb.1
    · intro hd
      refine ⟨M.alpha d, List.mem_reverse.mpr ((boundary.cycle_mem_iff _).mpr
        ⟨not_not.mp fun h => hd.2 ((hout _).mpr h), ?_⟩), M.alpha_involutive d⟩
      rw [M.alpha_involutive d]
      exact (hout _).mp hd.1

theorem reverseAlpha_cycle (boundary : BoundaryCycle M faces)
    (hout : ∀ f, f ∈ outside ↔ f ∉ faces) :
    (boundary.reverseAlpha hout).cycle = boundary.cycle.reverse.map M.alpha :=
  rfl

/-- **The complement cycle follows the boundary.**  For an unpinched face set whose cycle follows
the boundary, the successor of `alpha x` on the complement cycle is `alpha` of the predecessor of
`x`, and the complement walk joins them by `Unpinched.boundaryWalk_alpha`. -/
theorem reverseAlpha_followsBoundary (boundary : BoundaryCycle M faces)
    (hout : ∀ f, f ∈ outside ↔ f ∉ faces) (hwalk : boundary.FollowsBoundary)
    (hpinch : Unpinched M faces) : (boundary.reverseAlpha hout).FollowsBoundary := by
  classical
  intro x
  rw [boundaryPerm_apply_val]
  have hxmem : x.1 ∈ (boundary.reverseAlpha hout).cycle :=
    ((boundary.reverseAlpha hout).cycle_mem_iff x.1).mpr x.2
  have he : IsBoundaryDart M faces (M.alpha x.1) := by
    have hx := x.2
    refine ⟨not_not.mp fun h => hx.2 ((hout _).mpr h), ?_⟩
    rw [M.alpha_involutive x.1]
    exact (hout _).mp hx.1
  have hemem : M.alpha x.1 ∈ boundary.cycle := (boundary.cycle_mem_iff _).mpr he
  have hd : IsBoundaryDart M faces (boundary.cycle.prev (M.alpha x.1) hemem) :=
    (boundary.cycle_mem_iff _).mp (List.prev_mem _ _ _)
  have hnext : (boundary.reverseAlpha hout).cycle.next x.1 hxmem =
      M.alpha (boundary.cycle.prev (M.alpha x.1) hemem) := by
    rw [← List.next_reverse_eq_prev boundary.cycle boundary.cycle_nodup (M.alpha x.1) hemem]
    exact next_map_of_injective M.alpha_involutive.injective
      (List.nodup_reverse.mpr boundary.cycle_nodup) (List.mem_reverse.mpr hemem)
      (M.alpha_involutive x.1) hxmem
  have hw : BoundaryWalk M faces (boundary.cycle.prev (M.alpha x.1) hemem) (M.alpha x.1) := by
    have h := hwalk ⟨_, hd⟩
    rw [boundaryPerm_apply_val, List.next_prev boundary.cycle boundary.cycle_nodup _ hemem] at h
    exact h
  have h := hpinch.boundaryWalk_alpha hout hd he hw
  rw [M.alpha_involutive x.1] at h
  rw [hnext]
  exact h

end BoundaryCycle

end Surgery.MapCollapse

namespace PocketRegion

open Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- **The pocket region of an unpinched face set.**  An unpinched face set away from the exterior
face, with a disc region whose cycle follows the boundary, is a pocket region.  The complement's
cycle is the face set's cycle reversed across the edges, so its inverse is the face set's cycle
itself. -/
noncomputable def ofUnpinched (faces outside : Finset Delta.toCombMap.Face)
    (hout : ∀ f, f ∈ outside ↔ f ∉ faces) (houter : Delta.outerFace ∈ outside)
    (inner : IsDiscRegion Delta.toCombMap faces) (hwalk : inner.FollowsBoundary)
    (hpinch : Unpinched Delta.toCombMap faces) : PocketRegion Delta where
  faces := faces
  outside := outside
  mem_outside_iff := hout
  outerFace_mem := houter
  inner := inner
  outer := (inner.toBoundaryCycle.reverseAlpha hout).toDiscRegion_of_followsBoundary
    Delta.toCombMap outside
    (inner.toBoundaryCycle.reverseAlpha_followsBoundary hout hwalk hpinch) Delta.planar
  invDarts_outer_rotate :=
    ⟨0, (Embedded.invDarts_invDarts inner.cycle).trans (List.rotate_zero _).symm⟩

theorem ofUnpinched_faces (faces outside : Finset Delta.toCombMap.Face)
    (hout : ∀ f, f ∈ outside ↔ f ∉ faces) (houter : Delta.outerFace ∈ outside)
    (inner : IsDiscRegion Delta.toCombMap faces) (hwalk : inner.FollowsBoundary)
    (hpinch : Unpinched Delta.toCombMap faces) :
    (ofUnpinched faces outside hout houter inner hwalk hpinch).faces = faces :=
  rfl

theorem ofUnpinched_inner (faces outside : Finset Delta.toCombMap.Face)
    (hout : ∀ f, f ∈ outside ↔ f ∉ faces) (houter : Delta.outerFace ∈ outside)
    (inner : IsDiscRegion Delta.toCombMap faces) (hwalk : inner.FollowsBoundary)
    (hpinch : Unpinched Delta.toCombMap faces) :
    (ofUnpinched faces outside hout houter inner hwalk hpinch).inner = inner :=
  rfl

/-- The inverse complement cycle of the pocket is the face set's cycle. -/
theorem ofUnpinched_invDarts_outer (faces outside : Finset Delta.toCombMap.Face)
    (hout : ∀ f, f ∈ outside ↔ f ∉ faces) (houter : Delta.outerFace ∈ outside)
    (inner : IsDiscRegion Delta.toCombMap faces) (hwalk : inner.FollowsBoundary)
    (hpinch : Unpinched Delta.toCombMap faces) :
    Embedded.invDarts Delta (ofUnpinched faces outside hout houter inner hwalk hpinch).outer.cycle =
      inner.cycle :=
  Embedded.invDarts_invDarts inner.cycle

/-- The complement cycle of the pocket follows the boundary. -/
theorem ofUnpinched_outer_followsBoundary (faces outside : Finset Delta.toCombMap.Face)
    (hout : ∀ f, f ∈ outside ↔ f ∉ faces) (houter : Delta.outerFace ∈ outside)
    (inner : IsDiscRegion Delta.toCombMap faces) (hwalk : inner.FollowsBoundary)
    (hpinch : Unpinched Delta.toCombMap faces) :
    (ofUnpinched faces outside hout houter inner hwalk hpinch).outer.FollowsBoundary :=
  inner.toBoundaryCycle.reverseAlpha_followsBoundary hout hwalk hpinch

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.unpinched_iff_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.exists_component_of_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.isSimpleClosedWalk_of_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.unpinched_of_isSimpleClosedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.reverseAlpha_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.ofUnpinched_invDarts_outer
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.ofUnpinched_outer_followsBoundary
