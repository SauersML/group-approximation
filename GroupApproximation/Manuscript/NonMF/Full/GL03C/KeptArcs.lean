import GroupApproximation.Manuscript.NonMF.Full.GL03C.FourthJunction

/-!
# The kept parts of both arcs are arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, where `t_1` and `t_2` are subarcs of the old arcs.  This is
infrastructure for `thm:hull` in `non_mf_groups_exist.tex` (around line 2121).

A region move (`GL05b.movePred`) keeps an end block of each arc of a pocket boundary
(`GL05b.IsEndBlock`).  This module turns the two end blocks into cyclic arcs and assembles the
closed-walk tail of `GL06f.RoseRegionMoveSubArcStatement`.

* `exists_take_arc`, `exists_drop_arc_of_le`, `exists_drop_arc`: a prefix or a suffix of a
  cyclic arc is a cyclic arc.  A prefix keeps the start.  A suffix whose start does not pass the
  end of the carrier list stays inside the old arc.
* `exists_source_arc`: an end block of the reversed source arc is the reverse of an arc.
* `exists_target_arc`: an end block of the target arc, not wrapping when it is a suffix, is an arc
  inside the old one, so it keeps the bounds `lo ≤ start` and `start + length ≤ hi`.
* `regionMove_tail`: the tail clause of `GL06f.RoseRegionMoveSubArcStatement` for `source :=
  K.source`, from a nonempty kept list that is a walk in cycle order and the two end blocks.

Everything here is unconditional.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL03C

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

section Arcs

variable {Dart : Type v}

/-- **A prefix of a cyclic arc is a cyclic arc with the same start.** -/
theorem exists_take_arc {cycle : List Dart} (t : CyclicArc cycle) (i : ℕ) :
    ∃ t' : CyclicArc cycle, t'.start.1 = t.start.1 ∧ t'.length ≤ t.length ∧
      t'.darts = t.darts.take i := by
  have hst := t.start.2
  obtain ⟨t', hs, hl, hd⟩ := exists_infix_arc_of_le t (i := 0) (j := min i t.length)
    (by omega) (by omega)
  refine ⟨t', by omega, by omega, ?_⟩
  rw [hd, List.drop_zero, ← t.darts_length, ← List.take_take, List.take_length]

/-- **A suffix of a cyclic arc is a cyclic arc inside the old one**, when its start does not pass
the end of the carrier list. -/
theorem exists_drop_arc_of_le {cycle : List Dart} (t : CyclicArc cycle) (i : ℕ)
    (hs : t.start.1 + i ≤ cycle.length) :
    ∃ t' : CyclicArc cycle, t.start.1 ≤ t'.start.1 ∧
      t'.start.1 + t'.length ≤ t.start.1 + t.length ∧ t'.darts = t.darts.drop i := by
  have hdl := t.darts_length
  by_cases hi : i ≤ t.length
  · obtain ⟨t', hst, hl, hd⟩ := exists_infix_arc_of_le t (i := i) (j := t.length - i)
      (by omega) hs
    refine ⟨t', by omega, by omega, ?_⟩
    rw [hd]
    apply List.take_of_length_le
    rw [List.length_drop]
    omega
  · have hnil : t.darts.drop i = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨zeroArc t.start, Nat.le_refl _, ?_, ?_⟩
    · show t.start.1 + 0 ≤ t.start.1 + t.length
      omega
    · rw [zeroArc_darts, hnil]

/-- **A suffix of a cyclic arc is a cyclic arc, not longer than the arc** (it may wrap). -/
theorem exists_drop_arc {cycle : List Dart} (t : CyclicArc cycle) (i : ℕ) :
    ∃ t' : CyclicArc cycle, t'.length ≤ t.length ∧ t'.darts = t.darts.drop i := by
  have hdl := t.darts_length
  by_cases hi : i ≤ t.length
  · obtain ⟨t', hl, hd⟩ := exists_infix_arc t (i := i) (j := t.length - i) (by omega)
    refine ⟨t', by omega, ?_⟩
    rw [hd]
    apply List.take_of_length_le
    rw [List.length_drop]
    omega
  · have hnil : t.darts.drop i = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨zeroArc t.start, Nat.zero_le _, ?_⟩
    rw [zeroArc_darts, hnil]

/-- **An end block of a cyclic arc is an arc inside the old one**, when a suffix block does not
pass the end of the carrier list. -/
theorem exists_target_arc {cycle : List Dart} (t : CyclicArc cycle) (p : Dart → Bool)
    (h : ∃ i, t.darts.filter p = t.darts.take i ∨
      (t.darts.filter p = t.darts.drop i ∧ t.start.1 + i ≤ cycle.length)) :
    ∃ t' : CyclicArc cycle, t.start.1 ≤ t'.start.1 ∧
      t'.start.1 + t'.length ≤ t.start.1 + t.length ∧ t.darts.filter p = t'.darts := by
  obtain ⟨i, hi | ⟨hi, hs⟩⟩ := h
  · obtain ⟨t', hst, hl, hd⟩ := exists_take_arc t i
    refine ⟨t', by omega, by omega, ?_⟩
    rw [hd]
    exact hi
  · obtain ⟨t', h1, h2, hd⟩ := exists_drop_arc_of_le t i hs
    refine ⟨t', h1, h2, ?_⟩
    rw [hd]
    exact hi

/-- An end block of an arc that does not wrap is an end block whose suffix case does not pass the
end of the carrier list. -/
theorem noWrapEndBlock_of_isEndBlock {cycle : List Dart} (t : CyclicArc cycle) (p : Dart → Bool)
    (h : GL05b.IsEndBlock p t.darts) (hw : t.start.1 + t.length ≤ cycle.length) :
    ∃ i, t.darts.filter p = t.darts.take i ∨
      (t.darts.filter p = t.darts.drop i ∧ t.start.1 + i ≤ cycle.length) := by
  obtain ⟨i, hi | hi⟩ := h
  · exact ⟨i, Or.inl hi⟩
  · by_cases hle : i ≤ t.length
    · exact ⟨i, Or.inr ⟨hi, by omega⟩⟩
    · have hdl := t.darts_length
      have h1 : t.darts.drop i = [] := List.drop_eq_nil_of_le (by omega)
      have h2 : t.darts.drop t.length = [] := List.drop_eq_nil_of_le (by omega)
      refine ⟨t.length, Or.inr ⟨?_, hw⟩⟩
      rw [hi, h1, h2]

end Arcs

section InvDarts

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}

/-- A prefix of a reversed list is the reverse of a suffix. -/
theorem take_invDarts (X : DiscDiagram.{u, w, v} W) (l : List X.toCombMap.Dart) (i : ℕ) :
    (invDarts X l).take i = invDarts X (l.drop (l.length - i)) := by
  show (l.reverse.map X.toCombMap.alpha).take i =
    (l.drop (l.length - i)).reverse.map X.toCombMap.alpha
  rw [← List.map_take, List.take_reverse]

/-- A suffix of a reversed list is the reverse of a prefix. -/
theorem drop_invDarts (X : DiscDiagram.{u, w, v} W) (l : List X.toCombMap.Dart) (i : ℕ) :
    (invDarts X l).drop i = invDarts X (l.take (l.length - i)) := by
  show (l.reverse.map X.toCombMap.alpha).drop i =
    (l.take (l.length - i)).reverse.map X.toCombMap.alpha
  rw [← List.map_drop, List.drop_reverse]

/-- Reversing a dart list is injective. -/
theorem invDarts_inj (X : DiscDiagram.{u, w, v} W) {a b : List X.toCombMap.Dart}
    (h : invDarts X a = invDarts X b) : a = b := by
  have h' : a.reverse.map X.toCombMap.alpha = b.reverse.map X.toCombMap.alpha := h
  exact List.reverse_inj.mp
    ((List.map_inj_right fun x y hxy => X.toCombMap.alpha.injective hxy).mp h')

/-- **An end block of a reversed arc is the reverse of an arc, not longer than the arc.** -/
theorem exists_source_arc (X : DiscDiagram.{u, w, v} W) {cycle : List X.toCombMap.Dart}
    (t : CyclicArc cycle) (p : X.toCombMap.Dart → Bool)
    (h : GL05b.IsEndBlock p (invDarts X t.darts)) :
    ∃ t' : CyclicArc cycle, t'.length ≤ t.length ∧
      t.darts.filter (fun d => p (X.toCombMap.alpha d)) = t'.darts := by
  obtain ⟨i, hi | hi⟩ := h
  · rw [filter_invDarts, take_invDarts] at hi
    obtain ⟨t', hl, hd⟩ := exists_drop_arc t (t.darts.length - i)
    refine ⟨t', hl, ?_⟩
    rw [hd]
    exact invDarts_inj X hi
  · rw [filter_invDarts, drop_invDarts] at hi
    obtain ⟨t', -, hl, hd⟩ := exists_take_arc t (t.darts.length - i)
    refine ⟨t', hl, ?_⟩
    rw [hd]
    exact invDarts_inj X hi

/-- **The closed-walk tail of a region move.**  Let a region move keep a nonempty list of darts
of the pocket boundary that is a walk in cycle order, and keep an end block of each arc, where the
suffix block of the target arc does not pass the end of the carrier.  Then the kept darts are
listed as a closed walk `s₁ t₁⁻¹ s₂ t₂` with `t₁` a proper subarc of the source cell, `t₂` a proper
subarc of the outer boundary between `lo` and `hi`, and sides of length at most `ε` (Osin 9.7(b)).
This is the tail clause of `GL06f.RoseRegionMoveSubArcStatement` for `source := K.source`. -/
theorem regionMove_tail {D : GGT.RelGenSet G Lambda} {eps lo hi : ℕ}
    {X : DiscDiagram.{u, w, v} W} (K : PocketFaceSet D eps X lo hi)
    {z : X.toCombMap.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y)
    (hind : ∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false)
    (hne : K.boundary.cycle.filter (GL05b.movePred X.toCombMap z) ≠ [])
    (hchain : (K.boundary.cycle.filter (GL05b.movePred X.toCombMap z)).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hsrcBlock : GL05b.IsEndBlock (GL05b.movePred X.toCombMap z)
      (invDarts X K.sourceArc.darts))
    (htgtBlock : ∃ i, K.targetArc.darts.filter (GL05b.movePred X.toCombMap z) =
        K.targetArc.darts.take i ∨
      (K.targetArc.darts.filter (GL05b.movePred X.toCombMap z) = K.targetArc.darts.drop i ∧
        K.targetArc.start.1 + i ≤ (outerDarts X).length))
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length) :
    ∃ (t₁ : CyclicArc (cellDarts X K.source)) (t₂ : CyclicArc (outerDarts X))
      (s₁ s₂ : List X.toCombMap.Dart),
      List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
        (K.boundary.cycle.filter (GL05b.movePred X.toCombMap z)) ∧
      IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ∧
      s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
      t₂.start.1 + t₂.length ≤ hi ∧
      t₁.length < (cellDarts X K.source).length ∧ t₂.length < (outerDarts X).length := by
  obtain ⟨t₁, hl₁, hA⟩ :=
    exists_source_arc X K.sourceArc (GL05b.movePred X.toCombMap z) hsrcBlock
  obtain ⟨t₂, hs₂, he₂, hB⟩ :=
    exists_target_arc K.targetArc (GL05b.movePred X.toCombMap z) htgtBlock
  obtain ⟨s₁, s₂, hperm, hwalk, hs₁len, hs₂len⟩ :=
    closedWalk_listing_of_filter K hz hind hne hchain hA hB
  have hlo := K.lo_le
  have hhi := K.le_hi
  exact ⟨t₁, t₂, s₁, s₂, hperm, hwalk, hs₁len, hs₂len, by omega, by omega, by omega, by omega⟩

/-- `regionMove_tail` with the target end block given as `GL05b.IsEndBlock` on a target arc that
does not wrap past the end of the outer boundary list. -/
theorem regionMove_tail_of_noWrap {D : GGT.RelGenSet G Lambda} {eps lo hi : ℕ}
    {X : DiscDiagram.{u, w, v} W} (K : PocketFaceSet D eps X lo hi)
    {z : X.toCombMap.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y)
    (hind : ∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false)
    (hne : K.boundary.cycle.filter (GL05b.movePred X.toCombMap z) ≠ [])
    (hchain : (K.boundary.cycle.filter (GL05b.movePred X.toCombMap z)).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hsrcBlock : GL05b.IsEndBlock (GL05b.movePred X.toCombMap z)
      (invDarts X K.sourceArc.darts))
    (htgtBlock : GL05b.IsEndBlock (GL05b.movePred X.toCombMap z) K.targetArc.darts)
    (hwrap : K.targetArc.start.1 + K.targetArc.length ≤ (outerDarts X).length)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length) :
    ∃ (t₁ : CyclicArc (cellDarts X K.source)) (t₂ : CyclicArc (outerDarts X))
      (s₁ s₂ : List X.toCombMap.Dart),
      List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
        (K.boundary.cycle.filter (GL05b.movePred X.toCombMap z)) ∧
      IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ∧
      s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
      t₂.start.1 + t₂.length ≤ hi ∧
      t₁.length < (cellDarts X K.source).length ∧ t₂.length < (outerDarts X).length :=
  regionMove_tail K hz hind hne hchain hsrcBlock
    (noWrapEndBlock_of_isEndBlock K.targetArc _ htgtBlock hwrap) hsrc htgt

end InvDarts

end GroupApproximation.Full.GL03C
