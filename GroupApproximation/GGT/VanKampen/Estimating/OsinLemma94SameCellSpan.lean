import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketSectionFaceSet
import GroupApproximation.Meta.AxiomGuard

/-!
# Arcs of one cell for the one-cell pairs of Lemma 9.4, Case 1

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, for a backwards connector pair whose source and
target sides lie across one relator cell `Π`.  The kills `false_of_sameCell_cellFree_pocketRegion_X`
and `_Y` take a pocket arc `A` of `Π` and an arc `T` of `Π` reading `q A p` (or `p A q`).  This
file supplies those arcs in the spelling of `CyclicArc.exists_spanArc`, where a gap arc starts
where the previous arc ends.

* `CyclicArc.exists_append_of_start_eq_rest` and `CyclicArc.exists_appendArc`: consecutive arcs
  whose total length fits in the carrier form one arc.
* `CyclicArc.darts_disjoint_of_nodup_walk`: arcs read backwards on a walk with no repeated dart
  share no dart.
* `CyclicArc.exists_spanArc_target_source` and `_source_target`: on the face walk
  `X ++ q⁻¹ ++ Y ++ p⁻¹` of `osinLemma94CaseOneWalk_sameCell`, a gap arc `A` starting where `q`
  (or `p`) ends, and an arc `T` reading `q A p` (or `p A q`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe v

namespace Embedded.CyclicArc

/-- **Two consecutive arcs.**  If `Y` starts where `X` ends and the two lengths fit in the carrier,
one arc with the start of `X` reads `X` and then `Y`. -/
theorem exists_append_of_start_eq_rest {Dart : Type v} {cycle : List Dart} (X Y : CyclicArc cycle)
    (hY : Y.start = X.rest.start) (hlen : X.length + Y.length ≤ cycle.length) :
    ∃ T : CyclicArc cycle, T.start = X.start ∧ T.length = X.length + Y.length ∧
      T.darts = X.darts ++ Y.darts := by
  refine ⟨⟨X.start, X.length + Y.length, hlen⟩, rfl, rfl, ?_⟩
  have e : ∀ arc : CyclicArc cycle, arc.darts = (cycle.rotate arc.start.1).take arc.length :=
    fun arc => congrArg (List.take arc.length) arc.rotated_eq_rotate
  have e1 : (⟨X.start, X.length + Y.length, hlen⟩ : CyclicArc cycle).darts =
      (cycle.rotate X.start.1).take (X.length + Y.length) := e _
  have hstart : Y.start.1 = (X.start.1 + X.length) % cycle.length := congrArg Fin.val hY
  have hX : X.length ≤ (cycle.rotate X.start.1).length := by
    rw [List.length_rotate]
    exact X.length_le
  have hYl : Y.length ≤ ((cycle.rotate X.start.1).drop X.length).length := by
    rw [List.length_drop, List.length_rotate]
    omega
  rw [e1, e X, e Y, List.take_add, hstart, List.rotate_mod, ← List.rotate_rotate,
    List.rotate_eq_drop_append_take hX, List.take_append_of_le_length hYl]

/-- **Three consecutive arcs.**  If `G` starts where `X` ends, `Y` starts where `G` ends, and the
three lengths fit in the carrier, one arc with the start of `X` reads `X`, `G` and `Y`.  With `G`
the pocket arc, this is the arc `T = q A p` of `false_of_sameCell_cellFree_pocketRegion_X`. -/
theorem exists_appendArc {Dart : Type v} {cycle : List Dart} (X G Y : CyclicArc cycle)
    (hG : G.start = X.rest.start) (hY : Y.start = G.rest.start)
    (hlen : X.length + G.length + Y.length ≤ cycle.length) :
    ∃ T : CyclicArc cycle, T.start = X.start ∧ T.length = X.length + G.length + Y.length ∧
      T.darts = X.darts ++ G.darts ++ Y.darts := by
  obtain ⟨U, hUs, hUl, hUd⟩ := exists_append_of_start_eq_rest X G hG (by omega)
  have hYU : Y.start = U.rest.start := by
    apply Fin.ext
    have hGv : G.start.1 = (X.start.1 + X.length) % cycle.length := congrArg Fin.val hG
    have hYv : Y.start.1 = (G.start.1 + G.length) % cycle.length := congrArg Fin.val hY
    show Y.start.1 = (U.start.1 + U.length) % cycle.length
    rw [hYv, hGv, Nat.mod_add_mod, hUs, hUl, Nat.add_assoc]
  obtain ⟨T, hTs, hTl, hTd⟩ := exists_append_of_start_eq_rest U Y hYU (by rw [hUl]; exact hlen)
  exact ⟨T, hTs.trans hUs, by rw [hTl, hUl], by rw [hTd, hUd]⟩

/-- **Arcs read backwards on one simple walk.**  If a walk `X ++ q⁻¹ ++ Y ++ p⁻¹` has no repeated
dart, the arcs `q` and `p` share no dart. -/
theorem darts_disjoint_of_nodup_walk {M : CombMap} {cycle : List M.Dart} (p q : CyclicArc cycle)
    {X Y : List M.Dart} (hnodup : (X ++ q.reverseDarts ++ Y ++ p.reverseDarts).Nodup) :
    ∀ d ∈ q.darts, d ∉ p.darts := by
  intro d hq hp
  have hq' : M.alpha d ∈ q.reverseDarts := by
    show M.alpha d ∈ q.darts.reverse.map M.alpha
    exact List.mem_map.mpr ⟨d, List.mem_reverse.mpr hq, rfl⟩
  have hp' : M.alpha d ∈ p.reverseDarts := by
    show M.alpha d ∈ p.darts.reverse.map M.alpha
    exact List.mem_map.mpr ⟨d, List.mem_reverse.mpr hp, rfl⟩
  exact (List.nodup_append.mp hnodup).2.2 _
    (List.mem_append_left Y (List.mem_append_right X hq')) _ hp' rfl

/-- **The spanning arc from the target arc.**  On a face walk `X ++ q⁻¹ ++ Y ++ p⁻¹` with `q`
nonempty, as in `osinLemma94CaseOneWalk_sameCell`, a gap arc `A` starts where `q` ends, and an arc
`T` with the start of `q` reads `q A p`.  These are the arcs `A` and `T` of
`false_of_sameCell_cellFree_pocketRegion_X`. -/
theorem exists_spanArc_target_source {M : CombMap} {f : M.Face} (B : FaceBoundary M f)
    {cycle : List M.Dart} (sourceArc targetArc : CyclicArc cycle) {X Y : List M.Dart} {r : ℕ}
    (htrav : B.darts.rotate r = X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    (htarget : 0 < targetArc.length) :
    ∃ A T : CyclicArc cycle, A.start = targetArc.rest.start ∧ T.start = targetArc.start ∧
      T.darts = targetArc.darts ++ A.darts ++ sourceArc.darts := by
  have hnodup : (X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts).Nodup := by
    rw [← htrav]
    exact List.nodup_rotate.mpr B.nodup
  exact exists_spanArc targetArc sourceArc htarget
    (darts_disjoint_of_nodup_walk sourceArc targetArc hnodup)

/-- **The spanning arc from the source arc.**  As `exists_spanArc_target_source`, with `p`
nonempty: a gap arc `A` starts where `p` ends, and an arc `T` with the start of `p` reads `p A q`.
These are the arcs `A` and `T` of `false_of_sameCell_cellFree_pocketRegion_Y`. -/
theorem exists_spanArc_source_target {M : CombMap} {f : M.Face} (B : FaceBoundary M f)
    {cycle : List M.Dart} (sourceArc targetArc : CyclicArc cycle) {X Y : List M.Dart} {r : ℕ}
    (htrav : B.darts.rotate r = X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    (hsource : 0 < sourceArc.length) :
    ∃ A T : CyclicArc cycle, A.start = sourceArc.rest.start ∧ T.start = sourceArc.start ∧
      T.darts = sourceArc.darts ++ A.darts ++ targetArc.darts := by
  have hnodup : (X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts).Nodup := by
    rw [← htrav]
    exact List.nodup_rotate.mpr B.nodup
  exact exists_spanArc sourceArc targetArc hsource
    (fun d hs ht => darts_disjoint_of_nodup_walk sourceArc targetArc hnodup d ht hs)

end Embedded.CyclicArc

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.exists_append_of_start_eq_rest
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.exists_appendArc
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.darts_disjoint_of_nodup_walk
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.exists_spanArc_target_source
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.exists_spanArc_source_target
