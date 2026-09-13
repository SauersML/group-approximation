import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionRotate
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The boundary cycle of a pocket region is a simple closed walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of
`Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

The collar step reads `∂Γ_1` as a walk that visits no vertex twice.  When both cycles of a pocket
region follow their boundary walks, the pocket's cycle is such a walk.  Take a boundary dart `d`
with predecessor `p`.  The pocket's boundary walk from `p` turns around the vertex of `d` from
`sigma (alpha p)` to `d` through darts internal to the pocket.  The complement's cycle lists the
reversed darts backwards, so its boundary walk from `alpha d` turns from `sigma d` to `alpha p`
through darts internal to the complement.  The two runs close up the rotation orbit of `d`, and a
boundary dart of the pocket on it is neither internal to either side nor `alpha p`, so it is `d`.

* `IsSimpleClosedWalk.of_next` and `IsSimpleClosedWalk.vertexOf_alpha_eq_next`: the chain and
  closing conditions say that each dart ends where its cyclic successor starts.
* `IsSimpleClosedWalk.rotate`: a cyclic permutation of a simple closed walk is one.
* `BoundaryCycle.eq_of_vertexOf_eq_of_complement`: the vertex argument, for a boundary cycle and a
  complement cycle that lists the reversed darts backwards.
* `PocketRegion.outer_next_alpha`: the successor of `alpha d` on the complement's cycle is
  `alpha` of the predecessor of `d`.
* `PocketRegion.isSimpleClosedWalk_inner_cycle` and
  `PocketRegion.isSimpleClosedWalk_invDarts_outer`: the pocket's cycle, and the inverse of the
  complement's cycle, are simple closed walks.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse

universe u w v

namespace IsSimpleClosedWalk

variable {M : CombMap.{v}} {walk : List M.Dart}

/-- **A simple closed walk from cyclic successors.**  A nonempty duplicate-free list of darts, each
ending where its cyclic successor starts, starting at distinct vertices and using no edge in both
directions, is a simple closed walk. -/
theorem of_next [DecidableEq M.Dart] (hne : walk ≠ []) (hnd : walk.Nodup)
    (hnext : ∀ d (hd : d ∈ walk), M.vertexOf (M.alpha d) = M.vertexOf (walk.next d hd))
    (hvert : (walk.map M.vertexOf).Nodup) (halpha : ∀ d ∈ walk, M.alpha d ∉ walk) :
    IsSimpleClosedWalk M walk where
  ne_nil := hne
  chain := by
    refine List.isChain_iff_getElem.mpr fun i hi => ?_
    have hi' : i + 1 < walk.length := by omega
    have h := hnext _ (List.getElem_mem (Nat.lt_of_succ_lt hi'))
    rw [List.next_getElem walk hnd i (Nat.lt_of_succ_lt hi')] at h
    simp only [Nat.mod_eq_of_lt hi'] at h
    exact h
  closes := by
    have h := hnext _ (List.getLast_mem hne)
    rw [List.next_getLast_eq_head walk hne hnd] at h
    exact h
  vertex_nodup := hvert
  alpha_not_mem := halpha

/-- Each dart of a simple closed walk ends where its cyclic successor starts. -/
theorem vertexOf_alpha_eq_next [DecidableEq M.Dart] (hw : IsSimpleClosedWalk M walk)
    {d : M.Dart} (hd : d ∈ walk) : M.vertexOf (M.alpha d) = M.vertexOf (walk.next d hd) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  rw [List.next_getElem walk hw.nodup i hi]
  by_cases hlast : i + 1 < walk.length
  · simp only [Nat.mod_eq_of_lt hlast]
    exact List.isChain_iff_getElem.mp hw.chain i (by omega)
  · have h := hw.closes
    simp only [List.getLast_eq_getElem, List.head_eq_getElem] at h
    simp only [show i + 1 = walk.length by omega, Nat.mod_self]
    obtain rfl : i = walk.length - 1 := by omega
    exact h

/-- **A cyclic permutation of a simple closed walk is a simple closed walk.** -/
theorem rotate (hw : IsSimpleClosedWalk M walk) (k : ℕ) :
    IsSimpleClosedWalk M (walk.rotate k) := by
  classical
  have hrot : walk ~r walk.rotate k := ⟨k, rfl⟩
  refine of_next (List.rotate_eq_nil_iff.not.mpr hw.ne_nil) (List.nodup_rotate.mpr hw.nodup)
    (fun d hd => ?_) ?_ ?_
  · have hd' : d ∈ walk := List.mem_rotate.mp hd
    exact (hw.vertexOf_alpha_eq_next hd').trans
      (congrArg M.vertexOf (List.isRotated_next_eq hrot hw.nodup hd'))
  · rw [List.map_rotate, List.nodup_rotate]
    exact hw.vertex_nodup
  · intro d hd hmem
    exact hw.alpha_not_mem d (List.mem_rotate.mp hd) (List.mem_rotate.mp hmem)

end IsSimpleClosedWalk

namespace Surgery.MapCollapse

variable {M : CombMap.{v}} {faces outside : Finset M.Face}

/-- A boundary walk from `d` ends at the vertex where `d` ends. -/
theorem BoundaryWalk.vertexOf_alpha_eq {d e : M.Dart} (h : BoundaryWalk M faces d e) :
    M.vertexOf (M.alpha d) = M.vertexOf e := by
  unfold BoundaryWalk at h
  induction h with
  | refl => exact (M.vertexOf_sigma (M.alpha d)).symm
  | tail _ hstep ih => rw [ih, ← hstep.2, M.vertexOf_sigma]

namespace BoundaryCycle

/-- A cycle that follows the boundary walks from each dart to its successor in the list. -/
theorem boundaryWalk_next [DecidableEq M.Dart] (boundary : BoundaryCycle M faces)
    (hwalk : boundary.FollowsBoundary) {d : M.Dart} (hd : d ∈ boundary.cycle) :
    BoundaryWalk M faces d (boundary.cycle.next d hd) := by
  have h := hwalk ⟨d, (boundary.cycle_mem_iff d).mp hd⟩
  rw [boundaryPerm_apply_val] at h
  exact h

/-- **Two boundary darts at one vertex are equal**, for a boundary cycle `inner` of `faces` and a
boundary cycle `outer` of the complement, both following the boundary, when the successor of
`alpha d` on `outer` is `alpha` of the predecessor `p` of `d` on `inner`.  The walk of `inner`
from `p` turns from `sigma (alpha p)` to `d₁` through darts internal to `faces`, and the walk of
`outer` from `alpha d₁` turns from `sigma d₁` to `alpha p` through darts internal to `outside`.
So the rotation orbit of `d₁` consists of `d₁`, darts internal to either side, and `alpha p`, and
the only boundary dart of `faces` among them is `d₁`. -/
theorem eq_of_vertexOf_eq_of_complement [DecidableEq M.Dart] (inner : BoundaryCycle M faces)
    (outer : BoundaryCycle M outside) (hmem : ∀ f, f ∈ outside ↔ f ∉ faces)
    (hin : inner.FollowsBoundary) (hout : outer.FollowsBoundary)
    (hnext : ∀ d (hd : d ∈ inner.cycle) (had : M.alpha d ∈ outer.cycle),
      outer.cycle.next (M.alpha d) had = M.alpha (inner.cycle.prev d hd))
    {d₁ d₂ : M.Dart} (h₁ : d₁ ∈ inner.cycle) (h₂ : d₂ ∈ inner.cycle)
    (hv : M.vertexOf d₁ = M.vertexOf d₂) : d₁ = d₂ := by
  have hb₁ := (inner.cycle_mem_iff d₁).mp h₁
  have hb₂ := (inner.cycle_mem_iff d₂).mp h₂
  have hp : inner.cycle.prev d₁ h₁ ∈ inner.cycle := List.prev_mem ..
  have hbp := (inner.cycle_mem_iff _).mp hp
  have had₁ : M.alpha d₁ ∈ outer.cycle := by
    refine (outer.cycle_mem_iff _).mpr ⟨(hmem _).mpr hb₁.2, ?_⟩
    rw [M.alpha_involutive d₁, hmem]
    exact not_not.mpr hb₁.1
  -- The run of `inner` from `sigma (alpha p)` to `d₁`.
  have hw₁ := inner.boundaryWalk_next hin hp
  rw [List.next_prev inner.cycle inner.cycle_nodup d₁ h₁] at hw₁
  obtain ⟨n₁, hn₁, hskip₁⟩ :=
    PermFirstReturn.exists_pow_of_skip_walk M.sigma (InternalDart M faces) hw₁
  -- The run of `outer` from `sigma d₁` to `alpha p`.
  have hw₂ := outer.boundaryWalk_next hout had₁
  rw [hnext d₁ h₁ had₁] at hw₂
  obtain ⟨n₂, hn₂, hskip₂⟩ :=
    PermFirstReturn.exists_pow_of_skip_walk M.sigma (InternalDart M outside) hw₂
  have hfa : M.facePerm (M.alpha d₁) = M.sigma d₁ := by
    change M.sigma (M.alpha (M.alpha d₁)) = M.sigma d₁
    rw [M.alpha_involutive d₁]
  rw [hfa] at hn₂ hskip₂
  -- The two runs close up the orbit.
  have hA : (M.sigma ^ (n₂ + 1)) d₁ = M.alpha (inner.cycle.prev d₁ h₁) := by
    rw [pow_succ, Perm.mul_apply]
    exact hn₂
  have hB : (M.sigma ^ (n₁ + 1)) (M.alpha (inner.cycle.prev d₁ h₁)) = d₁ := by
    rw [pow_succ, Perm.mul_apply]
    exact hn₁
  have hcyc : (M.sigma ^ (n₁ + 1 + (n₂ + 1))) d₁ = d₁ := by
    rw [pow_add, Perm.mul_apply, hA, hB]
  obtain ⟨j, hj⟩ := ((M.vertexOf_eq_iff d₁ d₂).mp hv).exists_nat_pow_eq
  have hmul : ∀ m : ℕ, (M.sigma ^ ((n₁ + 1 + (n₂ + 1)) * m)) d₁ = d₁ := fun m => by
    rw [pow_mul]
    exact Perm.pow_apply_eq_self_of_apply_eq_self hcyc m
  rw [← Nat.mod_add_div j (n₁ + 1 + (n₂ + 1)), pow_add, Perm.mul_apply, hmul] at hj
  obtain ⟨r, hr, hrd⟩ : ∃ r, r < n₁ + 1 + (n₂ + 1) ∧ (M.sigma ^ r) d₁ = d₂ :=
    ⟨_, Nat.mod_lt _ (by omega), hj⟩
  rcases Nat.eq_zero_or_pos r with rfl | _hr0
  · rw [pow_zero, Perm.one_apply] at hrd
    exact hrd
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [pow_succ, Perm.mul_apply] at hrd
  rcases lt_trichotomy k n₂ with hk | hk | hk
  · -- `d₂` is internal to `outside`.
    have hint := hskip₂ k hk
    rw [hrd] at hint
    exact ((hmem _).mp hint.1 hb₂.1).elim
  · -- `d₂` is `alpha p`.
    rw [hk, hn₂] at hrd
    rw [← hrd] at hb₂
    exact (hbp.2 hb₂.1).elim
  · -- `d₂` is internal to `faces`.
    obtain ⟨i, rfl⟩ : ∃ i, k = i + (n₂ + 1) := ⟨k - (n₂ + 1), by omega⟩
    rw [pow_add, Perm.mul_apply, pow_succ', Perm.mul_apply, hn₂] at hrd
    have hint := hskip₁ i (by omega)
    change InternalDart M faces ((M.sigma ^ i) (M.sigma (M.alpha (inner.cycle.prev d₁ h₁))))
      at hint
    rw [hrd] at hint
    exact (hb₂.2 hint.2).elim

end BoundaryCycle

end Surgery.MapCollapse

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- `List.prev` depends only on the list and the element. -/
private theorem prev_congr {α : Type*} [DecidableEq α] {l l' : List α} {x x' : α} (hl : l = l')
    (hx : x = x') (h : x ∈ l) (h' : x' ∈ l') : l.prev x h = l'.prev x' h' := by
  subst hl hx
  rfl

private theorem prev_map_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) {l : List α} (hl : l.Nodup) {a : α} (ha : a ∈ l)
    (hb : f a ∈ l.map f) : (l.map f).prev (f a) hb = f (l.prev a ha) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < (l.map f).length := by
    rw [List.length_map]
    exact hi
  have h := List.prev_getElem (l.map f) (List.Nodup.map hf hl) i hi'
  simp only [List.getElem_map, List.length_map] at h
  rw [h, List.prev_getElem l hl i hi]

/-- **The complement's successor.**  In a pocket region the successor of `alpha d` on the
complement's cycle is `alpha` of the predecessor of `d` on the pocket's cycle, since the inverse of
the complement's cycle is a cyclic permutation of the pocket's cycle. -/
theorem outer_next_alpha [DecidableEq Delta.toCombMap.Dart] (P : PocketRegion Delta)
    {d : Delta.toCombMap.Dart} (hd : d ∈ P.inner.cycle)
    (had : Delta.toCombMap.alpha d ∈ P.outer.cycle) :
    P.outer.cycle.next (Delta.toCombMap.alpha d) had =
      Delta.toCombMap.alpha (P.inner.cycle.prev d hd) := by
  obtain ⟨k, hk⟩ := P.invDarts_outer_rotate
  have hk' : P.outer.cycle.reverse.map Delta.toCombMap.alpha = P.inner.cycle.rotate k := hk
  have hrot : P.inner.cycle ~r P.inner.cycle.rotate k := ⟨k, rfl⟩
  have hrev : Delta.toCombMap.alpha d ∈ P.outer.cycle.reverse := List.mem_reverse.mpr had
  have hprev : P.inner.cycle.prev d hd =
      Delta.toCombMap.alpha (P.outer.cycle.next (Delta.toCombMap.alpha d) had) := by
    rw [List.isRotated_prev_eq hrot P.inner.cycle_nodup hd,
      prev_congr hk'.symm (Delta.toCombMap.alpha_involutive d).symm (List.mem_rotate.mpr hd)
        (List.mem_map_of_mem (f := Delta.toCombMap.alpha) hrev),
      prev_map_of_injective Delta.toCombMap.alpha_involutive.injective
        (List.nodup_reverse.mpr P.outer.cycle_nodup) hrev,
      List.prev_reverse_eq_next P.outer.cycle P.outer.cycle_nodup _ had]
  rw [hprev, Delta.toCombMap.alpha_involutive _]

/-- **Two boundary darts of a pocket at one vertex are equal**, when both cycles of the pocket
region follow their boundary walks. -/
theorem eq_of_vertexOf_eq (P : PocketRegion Delta) (hin : P.inner.FollowsBoundary)
    (hout : P.outer.FollowsBoundary) {d₁ d₂ : Delta.toCombMap.Dart} (h₁ : d₁ ∈ P.inner.cycle)
    (h₂ : d₂ ∈ P.inner.cycle)
    (hv : Delta.toCombMap.vertexOf d₁ = Delta.toCombMap.vertexOf d₂) : d₁ = d₂ := by
  classical
  exact P.inner.toBoundaryCycle.eq_of_vertexOf_eq_of_complement P.outer.toBoundaryCycle
    P.mem_outside_iff hin hout (fun _ hd had => P.outer_next_alpha hd had) h₁ h₂ hv

/-- **The pocket's cycle is a simple closed walk** once both cycles of the pocket region follow
their boundary walks. -/
theorem isSimpleClosedWalk_inner_cycle (P : PocketRegion Delta) (hin : P.inner.FollowsBoundary)
    (hout : P.outer.FollowsBoundary) : IsSimpleClosedWalk Delta.toCombMap P.inner.cycle := by
  classical
  refine IsSimpleClosedWalk.of_next P.inner.cycle_nonempty P.inner.cycle_nodup
    (fun d hd => (P.inner.toBoundaryCycle.boundaryWalk_next hin hd).vertexOf_alpha_eq) ?_ ?_
  · exact List.Nodup.map_on (fun x hx y hy hxy => P.eq_of_vertexOf_eq hin hout hx hy hxy)
      P.inner.cycle_nodup
  · intro d hd had
    exact ((P.inner.cycle_mem_iff d).mp hd).2 ((P.inner.cycle_mem_iff _).mp had).1

/-- **The inverse of the complement's cycle is a simple closed walk** once both cycles of the
pocket region follow their boundary walks: it is a cyclic permutation of the pocket's cycle. -/
theorem isSimpleClosedWalk_invDarts_outer (P : PocketRegion Delta)
    (hin : P.inner.FollowsBoundary) (hout : P.outer.FollowsBoundary) :
    IsSimpleClosedWalk Delta.toCombMap (Embedded.invDarts Delta P.outer.cycle) := by
  obtain ⟨k, hk⟩ := P.invDarts_outer_rotate
  rw [hk]
  exact (P.isSimpleClosedWalk_inner_cycle hin hout).rotate k

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsSimpleClosedWalk.of_next
#audit_axioms GroupApproximation.GGT.VanKampen.IsSimpleClosedWalk.vertexOf_alpha_eq_next
#audit_axioms GroupApproximation.GGT.VanKampen.IsSimpleClosedWalk.rotate
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryWalk.vertexOf_alpha_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.boundaryWalk_next
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.eq_of_vertexOf_eq_of_complement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.outer_next_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.eq_of_vertexOf_eq
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.isSimpleClosedWalk_inner_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.isSimpleClosedWalk_invDarts_outer
