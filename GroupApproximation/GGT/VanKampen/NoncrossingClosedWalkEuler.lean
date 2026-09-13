import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.GGT.VanKampen.SurgeryReclosedConnected
import GroupApproximation.GGT.VanKampen.PermFirstReturnOrbits
import GroupApproximation.GGT.VanKampen.CactusTopology
import Mathlib.Data.List.Cycle
import GroupApproximation.Meta.AxiomGuard

/-!
# The Euler characteristic of the inner side of a noncrossing closed walk

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

Using `Γ_1` as a disc subdiagram needs the map obtained by reclosing its faces to one face to be
planar.  For a noncrossing closed walk `w` in a planar map `M`, `NoncrossingClosedWalkSides.lean`
makes `w` a boundary cycle of the faces `sideFaces M w` on its side and the reversed walk a
boundary cycle of the other faces.  This module proves that reclosing the inner side preserves the
Euler characteristic once the outer cycle follows its face-set boundary
(`BoundaryCycle.FollowsBoundary`).  The hypothesis cannot be dropped: in the rose with darts
`0, …, 5`, `alpha = (0 1)(2 3)(4 5)` and `sigma : 1 ↦ 0 ↦ 3 ↦ 2 ↦ 5 ↦ 4 ↦ 1`, the walk `[0, 2, 4]`
is noncrossing, and reclosing its side gives a torus.

Following the outer cycle gives the vertices of the outer reclosing
(`reclosedMap_vertexCount`).  A retained dart `x` of the inner reclosing is classified by the walk
dart `alpha ((sigma ^ m) x)` for the first `m` at which old vertex rotation reaches a reversed walk
dart, or by its old vertex when there is none.  Following the outer cycle says that new rotation,
run from a walk dart, stops exactly there.  So the two reclosings together have `|w|` more vertices,
`|w|` more edges and two more faces than `M`, and the outer one is planar
(`reclosedMap_euler_preserved`).

* `IsNoncrossingClosedWalk.innerVertexClass`, `IsNoncrossingClosedWalk.innerVertexRep`: the vertex
  classifier of the inner reclosing.
* `IsNoncrossingClosedWalk.vertexCount_add`, `IsNoncrossingClosedWalk.edgeCount_add`,
  `IsNoncrossingClosedWalk.faceCount_add`: the counts of both reclosings.
* `IsNoncrossingClosedWalk.reclosed_euler`: the Euler equation of the inner reclosing, the input
  `heuler` of `PocketRegion.ofNoncrossingClosedWalk`.
* `IsNoncrossingClosedWalk.innerDiscRegion`: the inner side as a disc region.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

universe u

namespace NoncrossingClosedWalkEuler

/-- `finRotate n` moves a position to the next one, cyclically. -/
private theorem finRotate_val_eq_mod : ∀ {n : ℕ} (i : Fin n),
    (finRotate n i : ℕ) = (i.val + 1) % n
  | 0, i => i.elim0
  | n + 1, i => by
    rw [coe_finRotate]
    split_ifs with h
    · simp [h]
    · exact (Nat.mod_eq_of_lt (Nat.succ_lt_succ (Fin.val_lt_last h))).symm

private theorem facePerm_alpha_eq_sigma (M : CombMap.{u}) (d : M.Dart) :
    M.facePerm (M.alpha d) = M.sigma d := by
  change M.sigma (M.alpha (M.alpha d)) = M.sigma d
  rw [M.alpha_involutive d]

private theorem faceOf_sigma_eq_faceOf_alpha (M : CombMap.{u}) (d : M.Dart) :
    M.faceOf (M.sigma d) = M.faceOf (M.alpha d) := by
  rw [← facePerm_alpha_eq_sigma M d, M.faceOf_facePerm]

private theorem vertexOf_sigmaPow_eq (M : CombMap.{u}) (k : ℕ) (d : M.Dart) :
    M.vertexOf ((M.sigma ^ k) d) = M.vertexOf d := by
  induction k with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ k ih => rw [pow_succ', Perm.mul_apply, M.vertexOf_sigma, ih]

private theorem next_map_eq_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
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

/-- The first index satisfying a predicate that holds somewhere. -/
theorem exists_first_of_exists {P : ℕ → Prop} (h : ∃ k, P k) :
    ∃ m, P m ∧ ∀ j < m, ¬P j := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun j hj => Nat.find_min h hj⟩

/-- The first index satisfying a predicate is unique. -/
theorem first_unique {P : ℕ → Prop} {m n : ℕ} (hm : P m) (hmin : ∀ j < m, ¬P j) (hn : P n)
    (hnmin : ∀ j < n, ¬P j) : m = n := by
  rcases Nat.lt_trichotomy m n with h | h | h
  · exact absurd hm (hnmin m h)
  · exact h
  · exact absurd hn (hmin n h)

/-- The first reversed walk dart met by old vertex rotation. -/
theorem exists_first_hit {M : CombMap.{u}} {w : List M.Dart} {x : M.Dart}
    (h : ∃ k : ℕ, M.alpha ((M.sigma ^ k) x) ∈ w) :
    ∃ m : ℕ, M.alpha ((M.sigma ^ m) x) ∈ w ∧ ∀ j < m, M.alpha ((M.sigma ^ j) x) ∉ w :=
  exists_first_of_exists h

/-- A dart at a vertex without retained dart is internal. -/
theorem internal_of_not_exists {M : CombMap.{u}} {faces : Finset M.Face} {c : M.Vertex}
    (hc : ¬∃ d : KeptDart M faces, M.vertexOf d.1 = c) {d : M.Dart} (hd : M.vertexOf d = c) :
    InternalDart M faces d :=
  Classical.byContradiction fun h => hc ⟨⟨d, h⟩, hd⟩

/-- The darts of a map are those based inside a face set and those based outside it. -/
theorem dartCount_split (M : CombMap.{u}) (faces : Finset M.Face) :
    M.dartCount =
      Nat.card {d : M.Dart // M.faceOf d ∈ faces} + Nat.card (OutsideDart M faces) := by
  classical
  have h := Nat.card_congr (Equiv.sumCompl fun d : M.Dart => M.faceOf d ∈ faces)
  rw [Nat.card_sum] at h
  exact h.symm

/-- The darts based outside the faces on the other side of a walk are the darts based on its
side. -/
theorem card_outsideDart_sideOutside (M : CombMap.{u}) (w : List M.Dart) :
    Nat.card (OutsideDart M (sideOutside M w)) =
      Nat.card {d : M.Dart // M.faceOf d ∈ sideFaces M w} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun d => by
    rw [mem_sideOutside_iff, Classical.not_not])

variable {M : CombMap.{u}} {faces : Finset M.Face}

private theorem positionEquiv_val_eq_getElem (boundary : BoundaryCycle M faces)
    (i : Fin boundary.cycle.length) :
    (boundary.positionEquiv i : M.Dart) = boundary.cycle[i.val] :=
  rfl

private theorem boundaryPerm_val_eq_next [DecidableEq M.Dart] (boundary : BoundaryCycle M faces)
    (x : BoundaryDart M faces) :
    (boundary.boundaryPerm x : M.Dart) =
      boundary.cycle.next x.1 ((boundary.cycle_mem_iff x.1).mpr x.2) := by
  obtain ⟨i, rfl⟩ := boundary.positionEquiv.surjective x
  have hsucc : (boundary.boundaryPerm (boundary.positionEquiv i) : M.Dart) =
      boundary.cycle[(i.val + 1) % boundary.cycle.length]'
        (Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)) := by
    simp only [BoundaryCycle.boundaryPerm, Equiv.trans_apply, Equiv.symm_apply_apply,
      positionEquiv_val_eq_getElem, finRotate_val_eq_mod]
  rw [hsucc]
  exact (List.next_getElem boundary.cycle boundary.cycle_nodup i.val i.isLt).symm

/-- A boundary cycle has as many darts as the boundary. -/
theorem card_boundaryDart (boundary : BoundaryCycle M faces) :
    Nat.card (BoundaryDart M faces) = boundary.cycle.length :=
  (Nat.card_congr boundary.positionEquiv.symm).trans (Nat.card_fin _)

/-- The retained darts of a reclosing are the darts based outside the region and the boundary
darts. -/
theorem reclosed_dartCount (boundary : BoundaryCycle M faces) :
    (reclosedMap M faces boundary).dartCount =
      Nat.card (OutsideDart M faces) + boundary.cycle.length := by
  have h := Nat.card_congr (keptSplitEquiv M faces)
  rw [Nat.card_sum, card_boundaryDart boundary] at h
  exact h

theorem reclosed_facePerm_alpha_val (boundary : BoundaryCycle M faces) (x : KeptDart M faces) :
    ((reclosedMap M faces boundary).facePerm (keptAlpha M faces x)).1 =
      ((reclosedMap M faces boundary).sigma x).1 := by
  change ((reclosedMap M faces boundary).sigma (keptAlpha M faces (keptAlpha M faces x))).1 = _
  rw [keptAlpha_involutive M faces x]

/-- New rotation at a dart whose reversal is based outside the region is old rotation. -/
theorem reclosed_sigma_val_of_notMem (boundary : BoundaryCycle M faces) (x : KeptDart M faces)
    (hx : M.faceOf (M.alpha x.1) ∉ faces) :
    ((reclosedMap M faces boundary).sigma x).1 = M.sigma x.1 := by
  rw [← reclosed_facePerm_alpha_val boundary x,
    reclosedMap_facePerm_val_of_notMem M faces boundary (keptAlpha M faces x) hx]
  exact facePerm_alpha_eq_sigma M x.1

/-- New rotation at a dart whose reversal is based inside the region follows the boundary cycle
from that reversal. -/
theorem reclosed_sigma_val_of_mem (boundary : BoundaryCycle M faces) (x : KeptDart M faces)
    (hx : M.faceOf (M.alpha x.1) ∈ faces) :
    ((reclosedMap M faces boundary).sigma x).1 =
      (boundary.boundaryPerm
        ⟨M.alpha x.1, isBoundaryDart_of_mem M faces (keptAlpha M faces x) hx⟩).1 := by
  rw [← reclosed_facePerm_alpha_val boundary x]
  exact reclosedMap_facePerm_val_of_mem M faces boundary (keptAlpha M faces x) hx

/-- The vertices of the inner reclosing: an old vertex with no retained dart on the outer side,
or a walk dart. -/
abbrev InnerVertexIndex (M : CombMap.{u}) (w : List M.Dart) : Type u :=
  {c : M.Vertex // ¬∃ d : KeptDart M (sideOutside M w), M.vertexOf d.1 = c} ⊕
    {e : M.Dart // e ∈ w}

end NoncrossingClosedWalkEuler

open NoncrossingClosedWalkEuler

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

theorem faceOf_alpha_mem_iff (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {x : M.Dart} (hx : ¬InternalDart M (sideFaces M w) x) :
    M.faceOf (M.alpha x) ∈ sideFaces M w ↔ M.alpha x ∈ w := by
  rw [← hw.isBoundaryDart_sideFaces_iff hM (M.alpha x)]
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rw [M.alpha_involutive x]
    exact fun hx' => hx ⟨hx', h⟩
  · exact fun h => h.1

theorem alpha_notMem_of_internal (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {z : M.Dart} (hz : InternalDart M (sideOutside M w) z) : M.alpha z ∉ w := fun h =>
  (mem_sideOutside_iff M w _).mp hz.2 ((hw.isBoundaryDart_sideFaces_iff hM _).mpr h).1

/-- Old rotation from a retained dart stays on retained darts until it meets a reversed walk
dart. -/
theorem sigma_pow_not_internal (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : KeptDart M (sideFaces M w)) (m : ℕ)
    (hmin : ∀ j < m, M.alpha ((M.sigma ^ j) x.1) ∉ w) :
    ¬InternalDart M (sideFaces M w) ((M.sigma ^ m) x.1) := by
  induction m with
  | zero =>
    rw [pow_zero, Perm.one_apply]
    exact x.2
  | succ m ih =>
    have hy := ih fun j hj => hmin j (by omega)
    have hface : M.faceOf (M.alpha ((M.sigma ^ m) x.1)) ∉ sideFaces M w := fun h =>
      hmin m (by omega) ((hw.faceOf_alpha_mem_iff hM hy).mp h)
    intro hint
    have h1 := hint.1
    rw [pow_succ', Perm.mul_apply, faceOf_sigma_eq_faceOf_alpha] at h1
    exact hface h1

/-- A retained dart whose rotation never meets a reversed walk dart sits at a vertex with no
retained dart on the outer side. -/
theorem not_exists_outsideKept_of_avoid (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : KeptDart M (sideFaces M w)) (havoid : ∀ k : ℕ, M.alpha ((M.sigma ^ k) x.1) ∉ w) :
    ¬∃ d : KeptDart M (sideOutside M w), M.vertexOf d.1 = M.vertexOf x.1 := by
  rintro ⟨d, hd⟩
  have hcyc : M.sigma.SameCycle x.1 (M.sigma.symm d.1) :=
    Perm.sameCycle_apply_right.mp (by
      rw [Equiv.apply_symm_apply]
      exact (M.vertexOf_eq_iff _ _).mp hd.symm)
  obtain ⟨k, hk⟩ := hcyc.exists_nat_pow_eq
  have hd1 : d.1 = (M.sigma ^ (k + 1)) x.1 := by
    rw [pow_succ', Perm.mul_apply, hk, Equiv.apply_symm_apply]
  have hk0 := hw.sigma_pow_not_internal hM x k fun j _ => havoid j
  have hk1 := hw.sigma_pow_not_internal hM x (k + 1) fun j _ => havoid j
  have hf1 : M.faceOf d.1 ∉ sideFaces M w := by
    rw [hd1, pow_succ', Perm.mul_apply, faceOf_sigma_eq_faceOf_alpha]
    exact fun h => havoid k ((hw.faceOf_alpha_mem_iff hM hk0).mp h)
  have hf2 : M.faceOf (M.alpha d.1) ∉ sideFaces M w := by
    rw [hd1]
    exact fun h => havoid (k + 1) ((hw.faceOf_alpha_mem_iff hM hk1).mp h)
  exact d.2 ⟨(mem_sideOutside_iff M w _).mpr hf1, (mem_sideOutside_iff M w _).mpr hf2⟩

theorem avoid_of_not_exists (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {c : M.Vertex} (hc : ¬∃ d : KeptDart M (sideOutside M w), M.vertexOf d.1 = c)
    {x : M.Dart} (hx : M.vertexOf x = c) (k : ℕ) : M.alpha ((M.sigma ^ k) x) ∉ w :=
  hw.alpha_notMem_of_internal hM
    (internal_of_not_exists hc (by rw [vertexOf_sigmaPow_eq, hx]))

open Classical in
/-- **The vertex classifier of the inner reclosing.**  A retained dart `x` goes to the walk dart
`alpha ((sigma ^ m) x)` for the first `m` at which it lies on the walk, or to its old vertex when
there is no such `m`. -/
noncomputable def innerVertexClass (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : KeptDart M (sideFaces M w)) : InnerVertexIndex M w :=
  if h : ∃ k : ℕ, M.alpha ((M.sigma ^ k) x.1) ∈ w then
    Sum.inr ⟨M.alpha ((M.sigma ^ Classical.choose (exists_first_hit h)) x.1),
      (Classical.choose_spec (exists_first_hit h)).1⟩
  else Sum.inl ⟨M.vertexOf x.1, hw.not_exists_outsideKept_of_avoid hM x fun k hk => h ⟨k, hk⟩⟩

theorem innerVertexClass_eq_inr (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : KeptDart M (sideFaces M w)) (m : ℕ) {e : M.Dart} (he : e ∈ w)
    (hm : M.alpha ((M.sigma ^ m) x.1) = e)
    (hmin : ∀ j < m, M.alpha ((M.sigma ^ j) x.1) ∉ w) :
    hw.innerVertexClass hM x = Sum.inr ⟨e, he⟩ := by
  unfold innerVertexClass
  split_ifs with h
  · have hspec := Classical.choose_spec (exists_first_hit h)
    have heq : Classical.choose (exists_first_hit h) = m :=
      first_unique (P := fun k => M.alpha ((M.sigma ^ k) x.1) ∈ w) hspec.1 hspec.2
        (show M.alpha ((M.sigma ^ m) x.1) ∈ w by rw [hm]; exact he) hmin
    exact congrArg Sum.inr (Subtype.ext
      ((congrArg (fun k => M.alpha ((M.sigma ^ k) x.1)) heq).trans hm))
  · exact (h ⟨m, by rw [hm]; exact he⟩).elim

theorem innerVertexClass_eq_inl (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : KeptDart M (sideFaces M w)) (h : ∀ k : ℕ, M.alpha ((M.sigma ^ k) x.1) ∉ w) :
    hw.innerVertexClass hM x =
      Sum.inl ⟨M.vertexOf x.1, hw.not_exists_outsideKept_of_avoid hM x h⟩ := by
  unfold innerVertexClass
  split_ifs with h'
  · obtain ⟨k, hk⟩ := h'
    exact (h k hk).elim
  · rfl

/-- A representative retained dart of each vertex of the inner reclosing. -/
noncomputable def innerVertexRep (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    InnerVertexIndex M w → KeptDart M (sideFaces M w)
  | Sum.inl c => ⟨Quotient.out c.1, fun hint => (mem_sideOutside_iff M w _).mp
      (internal_of_not_exists (d := Quotient.out c.1) c.2 (Quotient.out_eq' c.1)).1 hint.1⟩
  | Sum.inr e => ⟨M.alpha e.1, fun hint =>
      ((hw.isBoundaryDart_sideFaces_iff hM e.1).mpr e.2).2 hint.1⟩

/-- Before rotation meets a reversed walk dart, new rotation is old rotation. -/
theorem innerSigma_pow_val (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : KeptDart M (sideFaces M w)) (m : ℕ)
    (hmin : ∀ j < m, M.alpha ((M.sigma ^ j) x.1) ∉ w) :
    (((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma ^ m) x).1 =
      (M.sigma ^ m) x.1 := by
  induction m with
  | zero => simp only [pow_zero, Perm.one_apply]
  | succ m ih =>
    have ih' := ih fun j hj => hmin j (by omega)
    have hface : M.faceOf (M.alpha
        (((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma ^ m) x).1) ∉
          sideFaces M w := by
      rw [ih']
      exact fun h => hmin m (by omega) ((hw.faceOf_alpha_mem_iff hM
        (hw.sigma_pow_not_internal hM x m fun j hj => hmin j (by omega))).mp h)
    rw [pow_succ', Perm.mul_apply, pow_succ', Perm.mul_apply,
      reclosed_sigma_val_of_notMem (hw.innerCycle hM) _ hface, ih']

/-- The successor of a walk dart on the inner cycle is the next walk dart. -/
theorem innerCycle_boundaryPerm_val [DecidableEq M.Dart] (hw : IsNoncrossingClosedWalk M w)
    (hM : M.IsPlanar) (x : BoundaryDart M (sideFaces M w)) :
    ((hw.innerCycle hM).boundaryPerm x).1 =
      w.next x.1 ((hw.isBoundaryDart_sideFaces_iff hM x.1).mp x.2) :=
  boundaryPerm_val_eq_next (hw.innerCycle hM) x

/-- The successor of a reversed walk dart on the outer cycle is the reversal of the walk dart
before it. -/
theorem outerCycle_boundaryPerm_val [DecidableEq M.Dart] (hw : IsNoncrossingClosedWalk M w)
    (hM : M.IsPlanar) (x : BoundaryDart M (sideOutside M w)) :
    ((hw.outerCycle hM).boundaryPerm x).1 =
      M.alpha (w.prev (M.alpha x.1) ((hw.isBoundaryDart_sideOutside_iff hM x.1).mp x.2)) := by
  have hemem : M.alpha x.1 ∈ w := (hw.isBoundaryDart_sideOutside_iff hM x.1).mp x.2
  have hxmem : x.1 ∈ w.reverse.map M.alpha := ((hw.outerCycle hM).cycle_mem_iff x.1).mpr x.2
  rw [boundaryPerm_val_eq_next (hw.outerCycle hM) x,
    ← List.next_reverse_eq_prev w hw.nodup (M.alpha x.1) hemem]
  exact next_map_eq_of_injective M.alpha_involutive.injective (List.nodup_reverse.mpr hw.nodup)
    (List.mem_reverse.mpr hemem) (M.alpha_involutive x.1) hxmem

/-- New rotation from a retained dart whose reversal is a walk dart keeps the class: the outer
cycle follows its boundary, so old rotation from the next walk dart returns to the walk. -/
theorem innerVertexClass_sigma_of_mem (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hout : (hw.outerCycle hM).FollowsBoundary) (x : KeptDart M (sideFaces M w))
    (ha : M.alpha x.1 ∈ w) :
    hw.innerVertexClass hM ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x) =
      hw.innerVertexClass hM x := by
  classical
  have hx : M.faceOf (M.alpha x.1) ∈ sideFaces M w := (hw.faceOf_alpha_mem_iff hM x.2).mpr ha
  have hsig : ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x).1 =
      w.next (M.alpha x.1) ha :=
    (reclosed_sigma_val_of_mem (hw.innerCycle hM) x hx).trans
      (hw.innerCycle_boundaryPerm_val hM _)
  have hfmem : w.next (M.alpha x.1) ha ∈ w := List.next_mem w _ ha
  have hb : IsBoundaryDart M (sideOutside M w) (M.alpha (w.next (M.alpha x.1) ha)) :=
    (hw.isBoundaryDart_sideOutside_iff hM _).mpr (by rw [M.alpha_involutive]; exact hfmem)
  have key : ∀ (b : M.Dart) (hb' : b ∈ w), b = w.next (M.alpha x.1) ha →
      w.prev b hb' = M.alpha x.1 := by
    rintro b hb' rfl
    exact List.prev_next w hw.nodup _ ha
  have hback : ((hw.outerCycle hM).boundaryPerm ⟨_, hb⟩).1 = x.1 := by
    rw [hw.outerCycle_boundaryPerm_val hM]
    show M.alpha (w.prev (M.alpha (M.alpha (w.next (M.alpha x.1) ha))) _) = x.1
    rw [key _ _ (M.alpha_involutive _), M.alpha_involutive x.1]
  have hwalk : BoundaryWalk M (sideOutside M w) (M.alpha (w.next (M.alpha x.1) ha))
      ((hw.outerCycle hM).boundaryPerm ⟨_, hb⟩).1 := hout ⟨_, hb⟩
  rw [hback] at hwalk
  unfold BoundaryWalk at hwalk
  rw [facePerm_alpha_eq_sigma M] at hwalk
  obtain ⟨n, hn, hskip⟩ :=
    PermFirstReturn.exists_pow_of_skip_walk M.sigma (InternalDart M (sideOutside M w)) hwalk
  have hstart := hw.innerVertexClass_eq_inr hM x 0 ha (by rw [pow_zero, Perm.one_apply])
    fun j hj => absurd hj (Nat.not_lt_zero j)
  refine Eq.trans ?_ hstart.symm
  refine hw.innerVertexClass_eq_inr hM
    ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x) (n + 1) ha ?_ ?_
  · rw [hsig, pow_succ, Perm.mul_apply, hn]
  · intro j hj
    rw [hsig]
    rcases j with _ | k
    · rw [pow_zero, Perm.one_apply]
      exact hw.alpha_not_mem _ hfmem
    · rw [pow_succ, Perm.mul_apply]
      exact hw.alpha_notMem_of_internal hM (hskip k (by omega))

/-- New rotation from a retained dart whose reversal is not a walk dart is old rotation, and it
keeps the class. -/
theorem innerVertexClass_sigma_of_notMem (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : KeptDart M (sideFaces M w)) (ha : M.alpha x.1 ∉ w) :
    hw.innerVertexClass hM ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x) =
      hw.innerVertexClass hM x := by
  have hsig : ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x).1 = M.sigma x.1 :=
    reclosed_sigma_val_of_notMem (hw.innerCycle hM) x fun h =>
      ha ((hw.faceOf_alpha_mem_iff hM x.2).mp h)
  have hshift : ∀ k : ℕ,
      M.alpha ((M.sigma ^ k) ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x).1) =
        M.alpha ((M.sigma ^ (k + 1)) x.1) := fun k => by
    rw [hsig, pow_succ, Perm.mul_apply]
  by_cases h : ∃ k : ℕ, M.alpha ((M.sigma ^ k) x.1) ∈ w
  · obtain ⟨m, hm, hmin⟩ := exists_first_hit h
    rcases m with _ | m
    · rw [pow_zero, Perm.one_apply] at hm
      exact absurd hm ha
    · exact (hw.innerVertexClass_eq_inr hM
        ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x) m hm (hshift m)
        fun j hj => by rw [hshift j]; exact hmin (j + 1) (by omega)).trans
          (hw.innerVertexClass_eq_inr hM x (m + 1) hm rfl hmin).symm
  · have havoid : ∀ k : ℕ, M.alpha ((M.sigma ^ k) x.1) ∉ w := fun k hk => h ⟨k, hk⟩
    have hvert : M.vertexOf ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x).1 =
        M.vertexOf x.1 := by
      rw [hsig, M.vertexOf_sigma]
    refine (hw.innerVertexClass_eq_inl hM
      ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x)
      fun k => by rw [hshift k]; exact havoid (k + 1)).trans
        (Eq.trans ?_ (hw.innerVertexClass_eq_inl hM x havoid).symm)
    exact congrArg Sum.inl (Subtype.ext hvert)

/-- The classifier is invariant under new rotation. -/
theorem innerVertexClass_sigma (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hout : (hw.outerCycle hM).FollowsBoundary) (x : KeptDart M (sideFaces M w)) :
    hw.innerVertexClass hM ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x) =
      hw.innerVertexClass hM x := by
  by_cases ha : M.alpha x.1 ∈ w
  · exact hw.innerVertexClass_sigma_of_mem hM hout x ha
  · exact hw.innerVertexClass_sigma_of_notMem hM x ha

/-- Each class is the class of its representative. -/
theorem innerVertexClass_rep (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (i : InnerVertexIndex M w) : hw.innerVertexClass hM (hw.innerVertexRep hM i) = i := by
  rcases i with c | e
  · have havoid : ∀ k : ℕ,
        M.alpha ((M.sigma ^ k) (hw.innerVertexRep hM (Sum.inl c)).1) ∉ w :=
      hw.avoid_of_not_exists hM c.2 (Quotient.out_eq' c.1)
    rw [hw.innerVertexClass_eq_inl hM (hw.innerVertexRep hM (Sum.inl c)) havoid]
    exact congrArg Sum.inl (Subtype.ext (Quotient.out_eq' c.1))
  · exact hw.innerVertexClass_eq_inr hM (hw.innerVertexRep hM (Sum.inr e)) 0 e.2
      (by rw [pow_zero, Perm.one_apply]; exact M.alpha_involutive e.1)
      fun j hj => absurd hj (Nat.not_lt_zero j)

/-- Every retained dart is on the new vertex of the representative of its class. -/
theorem innerVertexRep_sameCycle (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (d : KeptDart M (sideFaces M w)) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma.SameCycle
      (hw.innerVertexRep hM (hw.innerVertexClass hM d)) d := by
  by_cases h : ∃ k : ℕ, M.alpha ((M.sigma ^ k) d.1) ∈ w
  · obtain ⟨m, hm, hmin⟩ := exists_first_hit h
    rw [hw.innerVertexClass_eq_inr hM d m hm rfl hmin]
    have hrep : hw.innerVertexRep hM (Sum.inr ⟨_, hm⟩) =
        ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma ^ m) d := by
      apply Subtype.ext
      rw [hw.innerSigma_pow_val hM d m hmin]
      exact M.alpha_involutive ((M.sigma ^ m) d.1)
    rw [hrep]
    exact Perm.sameCycle_pow_left.mpr (Perm.SameCycle.refl _ _)
  · have havoid : ∀ k : ℕ, M.alpha ((M.sigma ^ k) d.1) ∉ w := fun k hk => h ⟨k, hk⟩
    rw [hw.innerVertexClass_eq_inl hM d havoid]
    have hq : M.vertexOf (Quotient.out (M.vertexOf d.1)) = M.vertexOf d.1 := Quotient.out_eq' _
    obtain ⟨k, hk⟩ := ((M.vertexOf_eq_iff _ _).mp hq).exists_nat_pow_eq
    refine ⟨(k : ℤ), ?_⟩
    have hc := hw.not_exists_outsideKept_of_avoid hM d havoid
    rw [zpow_natCast]
    apply Subtype.ext
    rw [hw.innerSigma_pow_val hM (hw.innerVertexRep hM (Sum.inl ⟨M.vertexOf d.1, hc⟩)) k
      fun j _ => hw.avoid_of_not_exists hM hc hq j]
    exact hk

/-- **The vertices of the inner reclosing**: the old vertices with no retained dart on the outer
side, and one vertex for each walk dart. -/
theorem inner_vertexCount (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hout : (hw.outerCycle hM).FollowsBoundary) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).vertexCount =
      Nat.card {c : M.Vertex // ¬∃ d : KeptDart M (sideOutside M w), M.vertexOf d.1 = c} +
        w.length := by
  have h := Nat.card_congr (OrbitClassifier.orbitEquiv
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma (hw.innerVertexClass hM)
    (hw.innerVertexRep hM) (hw.innerVertexClass_sigma hM hout) (hw.innerVertexClass_rep hM)
    (hw.innerVertexRep_sameCycle hM))
  have hw' : Nat.card {e : M.Dart // e ∈ w} = w.length :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun e =>
      (hw.isBoundaryDart_sideFaces_iff hM e).symm)).trans (card_boundaryDart (hw.innerCycle hM))
  rw [Nat.card_sum, hw'] at h
  exact h

/-- Both reclosings together have `|w|` more vertices than `M`. -/
theorem vertexCount_add (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hout : (hw.outerCycle hM).FollowsBoundary) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).vertexCount +
      (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).vertexCount =
        M.vertexCount + w.length := by
  have h1 := hw.inner_vertexCount hM hout
  have h2 := reclosedMap_vertexCount M (sideOutside M w) (hw.outerCycle hM) hout
  have hsplit :
      Nat.card {c : M.Vertex // ∃ d : KeptDart M (sideOutside M w), M.vertexOf d.1 = c} +
        Nat.card {c : M.Vertex // ¬∃ d : KeptDart M (sideOutside M w), M.vertexOf d.1 = c} =
          M.vertexCount := by
    classical
    have hcongr := Nat.card_congr (Equiv.sumCompl
      fun c : M.Vertex => ∃ d : KeptDart M (sideOutside M w), M.vertexOf d.1 = c)
    rw [Nat.card_sum] at hcongr
    exact hcongr
  omega

/-- Both reclosings together have `|w|` more edges than `M`. -/
theorem edgeCount_add (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).edgeCount +
      (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).edgeCount =
        M.edgeCount + w.length := by
  have h1 := reclosed_dartCount (hw.innerCycle hM)
  have h2 := reclosed_dartCount (hw.outerCycle hM)
  have h3 := dartCount_split M (sideFaces M w)
  have h4 := card_outsideDart_sideOutside M w
  have hlen : (hw.outerCycle hM).cycle.length = w.length := by
    show (w.reverse.map M.alpha).length = w.length
    rw [List.length_map, List.length_reverse]
  have hlen' : (hw.innerCycle hM).cycle.length = w.length := rfl
  rw [hlen'] at h1
  rw [hlen, h4] at h2
  have e1 := (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).dartCount_eq_two_mul_edgeCount
  have e2 := (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).dartCount_eq_two_mul_edgeCount
  have e3 := M.dartCount_eq_two_mul_edgeCount
  omega

/-- Both reclosings together have two more faces than `M`. -/
theorem faceCount_add (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).faceCount +
      (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).faceCount = M.faceCount + 2 := by
  classical
  have h1 := reclosedMap_faceCount M (sideFaces M w) (hw.innerCycle hM)
  have h2 := reclosedMap_faceCount M (sideOutside M w) (hw.outerCycle hM)
  have hI : Nat.card {f : M.Face // f ∈ sideFaces M w} = (sideFaces M w).card :=
    Nat.card_eq_finsetCard _
  have hO : Nat.card {f : M.Face // f ∈ sideOutside M w} = (sideOutside M w).card :=
    Nat.card_eq_finsetCard _
  have hO' : Nat.card {f : M.Face // f ∈ sideOutside M w} =
      Nat.card {f : M.Face // f ∉ sideFaces M w} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun f => mem_sideOutside_iff M w f)
  have hsplit : Nat.card {f : M.Face // f ∈ sideFaces M w} +
      Nat.card {f : M.Face // f ∉ sideFaces M w} = M.faceCount := by
    have hcongr := Nat.card_congr (Equiv.sumCompl fun f : M.Face => f ∈ sideFaces M w)
    rw [Nat.card_sum] at hcongr
    exact hcongr
  omega

/-- **The Euler equation of the inner reclosing.**  For a noncrossing closed walk `w` in a planar
map `M` whose outer cycle follows its face-set boundary, reclosing the faces on the side of `w`
to one face preserves the Euler characteristic. -/
theorem reclosed_euler (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hout : (hw.outerCycle hM).FollowsBoundary) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).eulerCharacteristic =
      M.eulerCharacteristic := by
  have hV := hw.vertexCount_add hM hout
  have hE := hw.edgeCount_add hM
  have hF := hw.faceCount_add hM
  have hχ := reclosedMap_euler_preserved M (sideOutside M w) (hw.outerCycle hM) hout hM
  have h2 := hM.2
  unfold CombMap.eulerCharacteristic at hχ h2 ⊢
  omega

/-- **The inner side of a noncrossing closed walk is a disc region** once the outer cycle follows
its boundary. -/
noncomputable def innerDiscRegion (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hout : (hw.outerCycle hM).FollowsBoundary) : IsDiscRegion M (sideFaces M w) :=
  BoundaryCycle.toDiscRegion_of_euler M (sideFaces M w) (hw.innerCycle hM) hM.1
    (hw.reclosed_euler hM hout)

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.inner_vertexCount
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.vertexCount_add
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.edgeCount_add
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.faceCount_add
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.reclosed_euler
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.innerDiscRegion
