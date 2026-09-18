import GroupApproximation.Manuscript.NonMF.Full.GL06c.FaceSetCut
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcSub
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketSectionFaceSet
import GroupApproximation.Meta.AxiomGuard

/-!
# Arcs and boundary cycles after cutting a region off a face set

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), and `thm:hull` (non_mf_groups_exist.tex,
"Hull's small cancellation theorem", ~2121).  When the region `Γ_{i,1}` whose arcs start the arcs
`t_1 ⊂ ∂Π` and `t_2 ⊂ q_1` of `∂Γ_1` is cut off `Γ_1`, the remaining face set has as arcs the rest
of `t_1` and the rest of `t_2`.

* `exists_dropArc`: the darts of an arc after a prefix form an arc of the same carrier.
* `exists_suffixArc`: an arc with the start of a longer arc splits the longer arc as itself
  followed by an arc of the rest.
* `targetBoundaryDarts_of_eq_none`: on the exterior face the target boundary darts are the darts
  of the target arc.
* `cutBoundary`: the boundary cycle `A ++ L⁻¹ ++ B` of `P \ R` from `FaceSetCut`.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex) through Osin's Lemma 9.7(b); certifies no
printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06c

open GroupApproximation.GGT.VanKampen GroupApproximation.GGT.VanKampen.Embedded

universe u w v

/-- **The rest of an arc after a prefix is an arc** (Osin Lemma 9.7(b), the rest of `t_1`).  If the
darts of `arc` are `l₁ ++ l₂`, then `l₂` are the darts of an arc of the same carrier. -/
theorem exists_dropArc {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle)
    (l₁ l₂ : List Dart) (h : arc.darts = l₁ ++ l₂) :
    ∃ t : CyclicArc cycle, t.darts = l₂ ∧ t.length = l₂.length := by
  have hlen : l₁.length + l₂.length ≤ arc.length := by
    have hl := congrArg List.length h
    rw [arc.darts_length, List.length_append] at hl
    omega
  refine ⟨arc.sub l₁.length l₂.length hlen, ?_, rfl⟩
  rw [CyclicArc.sub_darts, h, List.drop_left, List.take_length]

/-- **An initial arc splits off a longer arc** (Osin Lemma 9.7(b), the rest of `t_2`).  If `t` has
the start of `arc` and is not longer, the darts of `arc` are the darts of `t` followed by the darts
of an arc `β` that starts `t.length` positions later and has the remaining length. -/
theorem exists_suffixArc {Dart : Type v} {cycle : List Dart} (arc t : CyclicArc cycle)
    (hs : t.start.1 = arc.start.1) (hl : t.length ≤ arc.length) :
    ∃ β : CyclicArc cycle, arc.darts = t.darts ++ β.darts ∧
      β.start.1 = (arc.start.1 + t.length) % cycle.length ∧
        β.length = arc.length - t.length := by
  have hrot : t.rotated = arc.rotated := by
    show cycle.drop t.start.1 ++ cycle.take t.start.1 =
      cycle.drop arc.start.1 ++ cycle.take arc.start.1
    rw [hs]
  have htake : arc.darts.take t.length = t.darts := by
    show (arc.rotated.take arc.length).take t.length = t.rotated.take t.length
    rw [hrot, List.take_take, Nat.min_eq_left hl]
  have hdrop : (arc.darts.drop t.length).length ≤ arc.length - t.length :=
    Nat.le_of_eq (by rw [List.length_drop, arc.darts_length])
  refine ⟨arc.sub t.length (arc.length - t.length) (by omega), ?_, rfl, rfl⟩
  rw [CyclicArc.sub_darts, List.take_of_length_le hdrop, ← htake, List.take_append_drop]

section Cut

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- On the exterior face, the target boundary darts of a region are the darts of its target arc
(`thm:hull`: the arc of an exterior region on the section `q_1`). -/
theorem targetBoundaryDarts_of_eq_none (X : DiscDiagram.{u, w, v} W)
    {target : Option (Fin X.rCellCount)} (h : target = none)
    (arc : CyclicArc (targetDarts X target)) : targetBoundaryDarts X target arc = arc.darts := by
  subst h
  rfl

/-- **The boundary cycle of a face set with a region cut off** (`thm:hull`, Osin Lemma 9.7(b)).
Under the hypotheses of `mem_cut_iff` and `nodup_cut`, with `B` nonempty, `A ++ L⁻¹ ++ B` is a
boundary cycle of `P \ R`. -/
noncomputable def cutBoundary [DecidableEq X.toCombMap.Face] {P R : Finset X.toCombMap.Face}
    {A Mid L B : List X.toCombMap.Dart} (hB : B ≠ [])
    (hP : ∀ d, d ∈ A ++ Mid ++ B ↔
      (X.toCombMap.faceOf d ∈ P ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ P))
    (hR : ∀ d, d ∈ Mid ++ L ↔
      (X.toCombMap.faceOf d ∈ R ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ R))
    (hRP : R ⊆ P) (hnodup : (A ++ Mid ++ B).Nodup) (hRnodup : (Mid ++ L).Nodup)
    (hL : ∀ e ∈ L, e ∉ A ++ Mid ++ B) :
    Surgery.MapCollapse.BoundaryCycle X.toCombMap (P \ R) where
  cycle := A ++ invDarts X L ++ B
  cycle_nonempty := List.append_ne_nil_of_right_ne_nil _ hB
  cycle_nodup := nodup_cut hP hR hRP hnodup hRnodup
  cycle_mem_iff := mem_cut_iff hP hR hRP hnodup hL

/-- The cycle of `cutBoundary` is `A ++ L⁻¹ ++ B`. -/
theorem cutBoundary_cycle [DecidableEq X.toCombMap.Face] {P R : Finset X.toCombMap.Face}
    {A Mid L B : List X.toCombMap.Dart} (hB : B ≠ [])
    (hP : ∀ d, d ∈ A ++ Mid ++ B ↔
      (X.toCombMap.faceOf d ∈ P ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ P))
    (hR : ∀ d, d ∈ Mid ++ L ↔
      (X.toCombMap.faceOf d ∈ R ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ R))
    (hRP : R ⊆ P) (hnodup : (A ++ Mid ++ B).Nodup) (hRnodup : (Mid ++ L).Nodup)
    (hL : ∀ e ∈ L, e ∉ A ++ Mid ++ B) :
    (cutBoundary hB hP hR hRP hnodup hRnodup hL).cycle = A ++ invDarts X L ++ B :=
  rfl

end Cut

end GroupApproximation.Full.GL06c

#audit_axioms GroupApproximation.Full.GL06c.exists_dropArc
#audit_axioms GroupApproximation.Full.GL06c.exists_suffixArc
#audit_axioms GroupApproximation.Full.GL06c.targetBoundaryDarts_of_eq_none
#audit_axioms GroupApproximation.Full.GL06c.cutBoundary
#audit_axioms GroupApproximation.Full.GL06c.cutBoundary_cycle
