import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepWindingProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-60: the pinched winding residual from a planar model

Lane gl-p07-60.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepGenus_stepNext_of_model`: take a planar map `N` and a successor list `l'` on a face
  cycle `Γ`, and a word `w` with the order of `Γ` on `l'`.  Then every rotation step `(x, y)` of
  `l'.map ι` is a forward `StepNext` of `w`.
  * If `y'` follows `x'` in `Γ`, then `y` follows `x` in `w`.
  * Otherwise `Γ` rotates to `x' :: ((A₂ ++ D) ++ y' :: E)`.  The genus-zero first return
    (`witnessStepGenus_between_not_mem`) keeps `l'` out of `A₂ ++ D`.  An entry of `l` before
    `y` in `w` would come before `y'` in `Γ`, so it would lie in `D`.  Hence `y` is the first
    entry of `w` in `l`.
* `witnessStepGenus_pinched_of_bridge`: `WitnessStepWindingPinchedStatement` from
  `WitnessStepGenusBridgeStatement`, by `witnessStepDescent_bound_of_steps` (the first disjunct).
* `witnessStepGenus_skip_of_bridge`: the wire to `WitnessStepSkipStatement` through
  `witnessStepWinding_skip_of_pinched`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- A rotation step of a mapped list lifts to a rotation step of the list. -/
theorem witnessStepGenus_rotate_lift {α β : Type*} (f : α → β) (l' : List α) {n : ℕ}
    {s t : List β} {x y : β} (h : (l'.map f).rotate n = s ++ x :: y :: t) :
    ∃ (s' t' : List α) (x' y' : α), l'.rotate n = s' ++ x' :: y' :: t' ∧ f x' = x ∧ f y' = y := by
  rw [← List.map_rotate] at h
  obtain ⟨l₁, l₂, h₁, -, h₃⟩ := List.map_eq_append_iff.mp h
  obtain ⟨x', r, rfl, hx, hr⟩ := List.map_eq_cons_iff.mp h₃
  obtain ⟨y', t', rfl, hy, -⟩ := List.map_eq_cons_iff.mp hr
  exact ⟨l₁, t', x', y', h₁, hx, hy⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_rotate_lift

/-- The two ends of a rotation step of a duplicate-free list are distinct. -/
theorem witnessStepGenus_ne_of_rotate {α : Type*} {l : List α} (hl : l.Nodup) {n : ℕ}
    {s t : List α} {x y : α} (h : l.rotate n = s ++ x :: y :: t) : x ≠ y := by
  have hnd : (s ++ x :: y :: t).Nodup := by
    rw [← h]
    exact List.nodup_rotate.mpr hl
  have h2 := (List.nodup_append.mp hnd).2.1
  intro hxy
  exact (List.nodup_cons.mp h2).1 (by rw [hxy]; exact List.mem_cons.mpr (Or.inl rfl))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_ne_of_rotate

/-- **Steps of a planar successor model are forward `StepNext` steps.** -/
theorem witnessStepGenus_stepNext_of_model (N : CombMap.{u}) [DecidableEq N.Dart]
    (hN : N.IsPlanar) {β : Type*} (ι : N.Dart → β) {l' Γ : List N.Dart} (w : List β)
    (hl' : l'.Nodup)
    (hsucc : ∀ (n : ℕ) (s t : List N.Dart) (c d : N.Dart), l'.rotate n = s ++ c :: d :: t →
      WitnessStepGenusSucc N l' c d)
    (hΓ : N.IsFaceCycle Γ) (hsub : ∀ d ∈ l', d ∈ Γ)
    (hcompat : ∀ c ∈ l', ∀ d ∈ l',
      (WitnessStepGenusBefore w (ι c) (ι d) ↔ WitnessStepGenusBefore Γ c d))
    (hmem : ∀ d ∈ l', ι d ∈ w) :
    ∀ (n : ℕ) (s t : List β) (x y : β), (l'.map ι).rotate n = s ++ x :: y :: t →
      WitnessCurveSublistList.StepNext w (l'.map ι) x y := by
  intro n s t x y hr
  obtain ⟨s', t', x', y', hr', rfl, rfl⟩ := witnessStepGenus_rotate_lift ι l' hr
  have hx'l : x' ∈ l' := (List.mem_rotate (n := n)).mp (by rw [hr']; simp)
  have hy'l : y' ∈ l' := (List.mem_rotate (n := n)).mp (by rw [hr']; simp)
  have hxy := witnessStepGenus_ne_of_rotate hl' hr'
  obtain ⟨A₁, A₂, hA⟩ := List.append_of_mem (hsub x' hx'l)
  have hy'Γ := hsub y' hy'l
  rw [hA, List.mem_append, List.mem_cons] at hy'Γ
  rcases hy'Γ with hy1 | hy2 | hy3
  · obtain ⟨D, E, rfl⟩ := List.append_of_mem hy1
    have hrotΓ : Γ.rotate (D ++ y' :: E).length = x' :: ((A₂ ++ D) ++ y' :: E) := by
      rw [hA, List.rotate_append_length_eq]
      simp
    have hΓ' := hΓ.rotate (D ++ y' :: E).length
    rw [hrotΓ] at hΓ'
    have hfirst := witnessStepGenus_between_not_mem N hN hl' hsucc hr' hΓ'
    obtain ⟨u₀, z, hw⟩ := List.append_of_mem (hmem y' hy'l)
    refine Or.inr ⟨u₀, z, hw, ?_⟩
    intro e heu hel
    obtain ⟨t'', ht''l, rfl⟩ := List.mem_map.mp hel
    obtain ⟨u₁, v₁, hu⟩ := List.append_of_mem heu
    have hbef : WitnessStepGenusBefore w (ι t'') (ι y') := by
      refine ⟨u₁, v₁, z, ?_⟩
      rw [hw, hu, List.append_assoc, List.cons_append]
    obtain ⟨u₂, v₂, z₂, hΓt⟩ := (hcompat t'' ht''l y' hy'l).mp hbef
    have hndΓ : (D ++ y' :: (E ++ x' :: A₂)).Nodup := by
      have h := hΓ.nodup
      rw [hA, List.append_assoc, List.cons_append] at h
      exact h
    have hsplit : D ++ y' :: (E ++ x' :: A₂) = (u₂ ++ t'' :: v₂) ++ y' :: z₂ := by
      have h := hA.symm.trans hΓt
      rw [List.append_assoc, List.cons_append] at h
      rw [h, List.append_assoc, List.cons_append]
    have hD := (WitnessCurveSublistList.append_cons_inj_of_nodup hndΓ hsplit).1
    exact hfirst t'' (List.mem_append.mpr (Or.inr (by rw [hD]; simp))) ht''l
  · exact absurd hy2.symm hxy
  · obtain ⟨P, Q, rfl⟩ := List.append_of_mem hy3
    exact Or.inl ((hcompat x' hx'l y' hy'l).mpr ⟨A₁, P, Q, hA⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_stepNext_of_model

/-- **Lane gl-p07-60: the pinched winding residual from a planar model of the curve.** -/
theorem witnessStepGenus_pinched_of_bridge (h : WitnessStepGenusBridgeStatement.{u, w, v}) :
    WitnessStepWindingPinchedStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  classical
  obtain ⟨N, ι, l', Γ, hN, hmap, hsucc, hΓ, hsub, hcompat⟩ :=
    h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  have hl : (invDarts X outerWalk).Nodup := Embedded.invDarts_nodup E.nodup
  have hl' : l'.Nodup := List.Nodup.of_map ι (by rw [hmap]; exact hl)
  have hmem : ∀ d ∈ l', ι d ∈ witnessSublistCurve a b G₁ G₂ := fun d hd =>
    witnessSublist_mem_curve (hlab (ι d) (by rw [← hmap]; exact List.mem_map_of_mem hd))
  have hsteps := witnessStepGenus_stepNext_of_model N hN ι (witnessSublistCurve a b G₁ G₂) hl'
    hsucc hΓ hsub hcompat hmem
  rw [hmap] at hsteps
  exact Or.inl (witnessStepDescent_bound_of_steps (witnessSublist_curve_nodup a b G₁ G₂) hl
    hsteps)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_pinched_of_bridge

/-- **Lane gl-p07-60: the skip residual from a planar model of the curve.** -/
theorem witnessStepGenus_skip_of_bridge (h : WitnessStepGenusBridgeStatement.{u, w, v}) :
    WitnessStepSkipStatement.{u, w, v} :=
  witnessStepWinding_skip_of_pinched (witnessStepGenus_pinched_of_bridge h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_skip_of_bridge

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
