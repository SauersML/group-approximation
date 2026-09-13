import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegion
import GroupApproximation.GGT.VanKampen.FaceShelling
import Mathlib.Data.List.Cycle
import GroupApproximation.Meta.AxiomGuard

/-!
# Starting a pocket region at another boundary dart

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(a).  The four-section cut reads the boundary
of the pocket `Ξ` as `s_1 t_1 s_2 t_2`, starting at the first dart of `s_1`
(`OsinMultipleEdgeCut.ofPocketRegion` asks for that exact partition), while a disc region may
list its boundary cycle from any dart.  Collapsing a region sees its boundary cycle only through
the cyclic successor, so the listing may start anywhere.

* `BoundaryCycle.boundaryPerm_apply_val`: the cyclic successor of a boundary dart is its
  `List.next` in the cycle.
* `BoundaryCycle.ofIsRotated` and `BoundaryCycle.boundaryPerm_ofIsRotated`: a cyclic permutation
  of the cycle is a boundary cycle with the same successor.
* `reclosedMap_congr`, `reclosedMap_ofIsRotated`, `IsDiscRegion.ofIsRotated` and
  `replaceGRegion_ofIsRotated`: the reclosed map, and so the disc condition, is unchanged.
* `PocketRegion.withOuter`: the same pocket, with the complement's cycle listed so that its
  reverse is a prescribed cyclic permutation `l`; `PocketRegion.invDarts_withOuter_cycle` and
  `PocketRegion.withOuter_diagram_boundaryWord` say that the pocket then reads the word on `l`.
-/

namespace GroupApproximation.GGT.VanKampen

open Surgery.MapCollapse

universe u w v

namespace Surgery.MapCollapse

/-- `finRotate n` moves a position to the next one, cyclically. -/
private theorem finRotate_val : ∀ {n : ℕ} (i : Fin n), (finRotate n i : ℕ) = (i.val + 1) % n
  | 0, i => i.elim0
  | n + 1, i => by
    rw [coe_finRotate]
    split_ifs with h
    · simp [h]
    · exact (Nat.mod_eq_of_lt (Nat.succ_lt_succ (Fin.val_lt_last h))).symm

namespace BoundaryCycle

variable {M : CombMap} {faces : Finset M.Face}

/-- A position of a boundary cycle names the dart of the list at that position. -/
theorem positionEquiv_apply_val (boundary : BoundaryCycle M faces)
    (i : Fin boundary.cycle.length) :
    (boundary.positionEquiv i : M.Dart) = boundary.cycle[i.val] :=
  rfl

/-- **The successor on a boundary cycle is the next dart of the list.** -/
theorem boundaryPerm_apply_val [DecidableEq M.Dart] (boundary : BoundaryCycle M faces)
    (x : BoundaryDart M faces) :
    (boundary.boundaryPerm x : M.Dart) =
      boundary.cycle.next x.1 ((boundary.cycle_mem_iff x.1).mpr x.2) := by
  obtain ⟨i, rfl⟩ := boundary.positionEquiv.surjective x
  have hsucc : (boundary.boundaryPerm (boundary.positionEquiv i) : M.Dart) =
      boundary.cycle[(i.val + 1) % boundary.cycle.length]'
        (Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)) := by
    simp only [boundaryPerm, Equiv.trans_apply, Equiv.symm_apply_apply, positionEquiv_apply_val,
      finRotate_val]
  rw [hsucc]
  exact (List.next_getElem boundary.cycle boundary.cycle_nodup i.val i.isLt).symm

/-- **A cyclic permutation of a boundary cycle is a boundary cycle.** -/
def ofIsRotated (boundary : BoundaryCycle M faces) {l : List M.Dart}
    (h : boundary.cycle ~r l) : BoundaryCycle M faces where
  cycle := l
  cycle_nonempty := by
    intro hl
    subst hl
    exact boundary.cycle_nonempty (List.isRotated_nil_iff.mp h)
  cycle_nodup := h.nodup_iff.mp boundary.cycle_nodup
  cycle_mem_iff d := h.mem_iff.symm.trans (boundary.cycle_mem_iff d)

theorem ofIsRotated_cycle (boundary : BoundaryCycle M faces) {l : List M.Dart}
    (h : boundary.cycle ~r l) : (boundary.ofIsRotated h).cycle = l :=
  rfl

/-- **Rotating the listing does not change the cyclic successor.** -/
theorem boundaryPerm_ofIsRotated (boundary : BoundaryCycle M faces) {l : List M.Dart}
    (h : boundary.cycle ~r l) :
    (boundary.ofIsRotated h).boundaryPerm = boundary.boundaryPerm := by
  classical
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rw [boundaryPerm_apply_val, boundaryPerm_apply_val]
  exact (List.isRotated_next_eq h boundary.cycle_nodup
    ((boundary.cycle_mem_iff x.1).mpr x.2)).symm

end BoundaryCycle

/-- **Reclosing sees the boundary cycle only through its successor.** -/
theorem reclosedMap_congr (M : CombMap) (faces : Finset M.Face)
    {boundary boundary' : BoundaryCycle M faces}
    (h : boundary.boundaryPerm = boundary'.boundaryPerm) :
    reclosedMap M faces boundary = reclosedMap M faces boundary' := by
  unfold reclosedMap reclosedFacePerm
  rw [h]

/-- Rotating the listing of the boundary cycle does not change the reclosed map. -/
theorem reclosedMap_ofIsRotated (M : CombMap) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) {l : List M.Dart} (h : boundary.cycle ~r l) :
    reclosedMap M faces (boundary.ofIsRotated h) = reclosedMap M faces boundary :=
  reclosedMap_congr M faces (boundary.boundaryPerm_ofIsRotated h)

/-- **A cyclic permutation of the cycle of a disc region lists a disc region.** -/
def IsDiscRegion.ofIsRotated {M : CombMap} {faces : Finset M.Face}
    (region : IsDiscRegion M faces) {l : List M.Dart} (h : region.cycle ~r l) :
    IsDiscRegion M faces where
  toBoundaryCycle := region.toBoundaryCycle.ofIsRotated h
  reclosed_connected := by
    rw [reclosedMap_ofIsRotated]
    exact region.reclosed_connected
  euler_preserved := by
    rw [reclosedMap_ofIsRotated]
    exact region.euler_preserved

/-- Rotating the listing of a disc region does not change the replacement map. -/
theorem replaceGRegion_ofIsRotated (M : CombMap) (faces : Finset M.Face)
    (region : IsDiscRegion M faces) {l : List M.Dart} (h : region.cycle ~r l) :
    replaceGRegion M faces (region.ofIsRotated h) = replaceGRegion M faces region :=
  reclosedMap_ofIsRotated M faces region.toBoundaryCycle h

end Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w}

namespace Embedded

variable {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

/-- Reversing orientation preserves cyclic permutations. -/
theorem invDarts_isRotated {l l' : List Delta.toCombMap.Dart} (h : l ~r l') :
    invDarts Delta l ~r invDarts Delta l' :=
  h.reverse.map Delta.toCombMap.alpha

end Embedded

namespace PocketRegion

variable {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

/-- **The same pocket, with the complement's cycle started elsewhere.**  If `l` is a cyclic
permutation of the reversed boundary cycle of the complement, list that cycle so that its reverse
is exactly `l`.  The faces, the complement and the pocket's own cycle are unchanged. -/
def withOuter (P : PocketRegion Delta) {l : List Delta.toCombMap.Dart}
    (h : Embedded.invDarts Delta P.outer.cycle ~r l) : PocketRegion Delta where
  faces := P.faces
  outside := P.outside
  mem_outside_iff := P.mem_outside_iff
  outerFace_mem := P.outerFace_mem
  inner := P.inner
  outer := P.outer.ofIsRotated (l := Embedded.invDarts Delta l) (by
    have h' := Embedded.invDarts_isRotated h
    rwa [Embedded.invDarts_invDarts] at h')
  invDarts_outer_rotate := by
    obtain ⟨k, hk⟩ := P.invDarts_outer_rotate
    have hrot : P.inner.cycle ~r l :=
      List.IsRotated.trans (l' := Embedded.invDarts Delta P.outer.cycle) ⟨k, hk.symm⟩ h
    obtain ⟨n, hn⟩ := hrot
    exact ⟨n, (Embedded.invDarts_invDarts l).trans hn.symm⟩

theorem withOuter_faces (P : PocketRegion Delta) {l : List Delta.toCombMap.Dart}
    (h : Embedded.invDarts Delta P.outer.cycle ~r l) : (P.withOuter h).faces = P.faces :=
  rfl

theorem withOuter_outside (P : PocketRegion Delta) {l : List Delta.toCombMap.Dart}
    (h : Embedded.invDarts Delta P.outer.cycle ~r l) : (P.withOuter h).outside = P.outside :=
  rfl

/-- The reversed complement cycle of `P.withOuter h` is exactly `l`. -/
theorem invDarts_withOuter_cycle (P : PocketRegion Delta) {l : List Delta.toCombMap.Dart}
    (h : Embedded.invDarts Delta P.outer.cycle ~r l) :
    Embedded.invDarts Delta (P.withOuter h).outer.cycle = l :=
  Embedded.invDarts_invDarts l

/-- **The restarted pocket reads the word on `l`.** -/
theorem withOuter_diagram_boundaryWord (P : PocketRegion Delta) {l : List Delta.toCombMap.Dart}
    (h : Embedded.invDarts Delta P.outer.cycle ~r l) :
    (P.withOuter h).diagram.boundaryWord = Embedded.dartWord Delta l := by
  rw [diagram_boundaryWord, invDarts_withOuter_cycle]

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.positionEquiv_apply_val
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.boundaryPerm_apply_val
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.ofIsRotated
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.ofIsRotated_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.boundaryPerm_ofIsRotated
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.reclosedMap_congr
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.reclosedMap_ofIsRotated
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.IsDiscRegion.ofIsRotated
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.replaceGRegion_ofIsRotated
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.invDarts_isRotated
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.withOuter
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.withOuter_faces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.withOuter_outside
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.invDarts_withOuter_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.withOuter_diagram_boundaryWord
