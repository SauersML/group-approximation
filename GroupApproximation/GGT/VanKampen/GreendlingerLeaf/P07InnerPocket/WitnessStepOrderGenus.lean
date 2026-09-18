import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepOrderList
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepRecloseProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-63: a following boundary cycle reads the walk in order

Lane gl-p07-63.  Genus content for `FourPieceWitness.witnessStepReclose_OrderStatement`
(`WitnessStepRecloseProof.lean`).  Certifies no printed sentence on its own.  NOT COMPILED:
authored without running Lean.

* `witnessStepOrder_rotate_sublist`: let `ow` be an `EnclosedFaceSetSucc` walk of some face set,
  and `B` a boundary cycle of ANY face set `O` that follows its boundary and contains every dart
  of `ow`.  Then some rotation of `invDarts X ow` is a sublist of `invDarts X B.cycle`.  Proof:
  the planar model `witnessStepBridge_model` with `w' = invDarts X B.cycle` (compatibility is
  `Iff.rfl`), the step lemma `witnessStepGenus_stepNext_of_model`, and
  `exists_rotate_sublist_of_steps`.  Python: `SP/gl-p07-63/order_check.py`, 55719 planar cases
  (9116 with `O` not the complement of the face set), 0 failures; 6 failures in genus `≥ 1`.
* `witnessStepOrder_order_of_reclosed`: the Reclosed statement implies the Order statement.
* `witnessStepOrder_order_of_bridge`: the Bridge statement implies the Order statement.

## Status (LOUD)

With gl-p07-62 (`witnessStepReclose_reclosed_of_order`) and gl-p07-61
(`witnessStepBridge_of_reclosed`), this gives Order ⇔ Reclosed ⇔ Bridge.  **All three
gl-p07-60/61/62 residuals are equivalent**, so the chain does not reduce the order claim.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Rotating the inverse reading.**  A rotation of `invDarts X ow` is the inverse reading of a
rotation of `ow`. -/
theorem witnessStepOrder_invDarts_rotate {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W)
    (ow : List X.toCombMap.Dart) (n : ℕ) :
    (invDarts X ow).rotate n = invDarts X (ow.rotate (ow.length - n % ow.length)) := by
  show (ow.reverse.map X.toCombMap.alpha).rotate n =
    (ow.rotate (ow.length - n % ow.length)).reverse.map X.toCombMap.alpha
  rw [← List.map_rotate, List.rotate_reverse]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_invDarts_rotate

/-- **Inverse readings keep containment.** -/
theorem witnessStepOrder_invDarts_subset {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    {ow cyc : List X.toCombMap.Dart} (h : ∀ d ∈ ow, d ∈ cyc) :
    ∀ e ∈ invDarts X ow, e ∈ invDarts X cyc := by
  intro e he
  simp only [invDarts, List.mem_map, List.mem_reverse] at he ⊢
  obtain ⟨a, ha, rfl⟩ := he
  exact ⟨a, h a ha, rfl⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_invDarts_subset

/-- **A following boundary cycle through the walk reads it as a cyclic sublist.**  Genus
content: planarity of the reclosed map, through `witnessStepBridge_model`. -/
theorem witnessStepOrder_rotate_sublist {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X F ow) (O : Finset X.toCombMap.Face)
    (B : BoundaryCycle X.toCombMap O) (hwalk : B.FollowsBoundary)
    (hsub : ∀ d ∈ ow, d ∈ B.cycle) :
    ∃ n : ℕ, (invDarts X ow).rotate n <+ invDarts X B.cycle := by
  classical
  obtain ⟨N, ι, l', Γ, hN, hmap, hsucc, hΓ, hsub', hcompat⟩ :=
    witnessStepBridge_model E O B hwalk hsub (invDarts X B.cycle) fun _ _ _ _ => Iff.rfl
  have hl : (invDarts X ow).Nodup := Embedded.invDarts_nodup E.nodup
  have hl' : l'.Nodup := List.Nodup.of_map ι (by rw [hmap]; exact hl)
  have hin := witnessStepOrder_invDarts_subset hsub
  have hmem : ∀ d ∈ l', ι d ∈ invDarts X B.cycle := fun d hd =>
    hin (ι d) (by rw [← hmap]; exact List.mem_map_of_mem hd)
  have hsteps := witnessStepGenus_stepNext_of_model N hN ι (invDarts X B.cycle) hl' hsucc hΓ
    hsub' hcompat hmem
  rw [hmap] at hsteps
  exact WitnessCurveSublistList.exists_rotate_sublist_of_steps
    (Embedded.invDarts_nodup B.cycle_nodup) hl hin hsteps

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_rotate_sublist

/-- **Order through an injective-on-the-list map.**  If `P.map f` is duplicate free, `f`
carries the order of `P` on its entries to the order of `P.map f`, and back. -/
theorem witnessStepOrder_before_map_iff {α β : Type*} (f : α → β) {P : List α} {c d : α}
    (hP : (P.map f).Nodup) (hc : c ∈ P) (hd : d ∈ P) :
    WitnessStepGenusBefore (P.map f) (f c) (f d) ↔ WitnessStepGenusBefore P c d := by
  have hfwd : ∀ x y : α, WitnessStepGenusBefore P x y →
      WitnessStepGenusBefore (P.map f) (f x) (f y) := by
    rintro x y ⟨u, v, z, h⟩
    exact ⟨u.map f, v.map f, z.map f, by rw [h]; simp⟩
  constructor
  · intro h
    by_cases hcd : c = d
    · subst hcd
      exact absurd h (witnessStepOrder_before_asymm hP h)
    · rcases witnessStepOrder_before_total hc hd hcd with h' | h'
      · exact h'
      · exact absurd h (witnessStepOrder_before_asymm hP (hfwd d c h'))
  · exact hfwd c d

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_before_map_iff
/-- **Lane gl-p07-63: the Order statement from the Reclosed statement.**  The rotation `n` of
`witnessStepOrder_rotate_sublist` makes `(invDarts X outerWalk).rotate n` a sublist of
`invDarts X B.cycle`, which carries the order of the curve; `r = |ow| - n % |ow|`. -/
theorem witnessStepOrder_order_of_reclosed (h : witnessStepBridge_ReclosedStatement.{u, w, v}) :
    witnessStepReclose_OrderStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  obtain ⟨O, B, hwalk, hsub, hcompat⟩ :=
    h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  obtain ⟨n, hn⟩ := witnessStepOrder_rotate_sublist E O B hwalk hsub
  refine ⟨outerWalk.length - n % outerWalk.length, fun c hc d hd => ?_⟩
  rw [← witnessStepOrder_invDarts_rotate X outerWalk n]
  have hc' : c ∈ (invDarts X outerWalk).rotate n := List.mem_rotate.mpr hc
  have hd' : d ∈ (invDarts X outerWalk).rotate n := List.mem_rotate.mpr hd
  exact (hcompat c hc d hd).trans
    (witnessStepOrder_before_sublist_iff (Embedded.invDarts_nodup B.cycle_nodup) hn hc' hd')

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_order_of_reclosed

/-- **Lane gl-p07-63: the Order statement from the Bridge statement.**  Apply the step lemma to
the planar model with `ι = id` and curve `Γ`: a rotation of `l'` is a sublist of `Γ`.  Push it
through `ι` (injective on the duplicate-free `l'.map ι`). -/
theorem witnessStepOrder_order_of_bridge (h : WitnessStepGenusBridgeStatement.{u, w, v}) :
    witnessStepReclose_OrderStatement.{u, w, v} := by
  classical
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  obtain ⟨N, ι, l', Γ, hN, hmap, hsucc, hΓ, hsub, hcompat⟩ :=
    h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  have hl : (invDarts X outerWalk).Nodup := Embedded.invDarts_nodup E.nodup
  have hl' : l'.Nodup := List.Nodup.of_map ι (by rw [hmap]; exact hl)
  have hsteps := witnessStepGenus_stepNext_of_model N hN (id : N.Dart → N.Dart) Γ hl' hsucc
    hΓ hsub (fun _ _ _ _ => Iff.rfl) hsub
  rw [List.map_id] at hsteps
  obtain ⟨n, hn⟩ :=
    WitnessCurveSublistList.exists_rotate_sublist_of_steps hΓ.nodup hl' hsub hsteps
  refine ⟨outerWalk.length - n % outerWalk.length, fun c hc d hd => ?_⟩
  rw [← hmap] at hc hd
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
  rw [← witnessStepOrder_invDarts_rotate X outerWalk n, ← hmap, ← List.map_rotate]
  have hc'' : c' ∈ l'.rotate n := List.mem_rotate.mpr hc'
  have hd'' : d' ∈ l'.rotate n := List.mem_rotate.mpr hd'
  have hP : ((l'.rotate n).map ι).Nodup := by
    rw [List.map_rotate, hmap]
    exact List.nodup_rotate.mpr hl
  exact (hcompat c' hc' d' hd').trans
    ((witnessStepOrder_before_sublist_iff hΓ.nodup hn hc'' hd'').trans
      (witnessStepOrder_before_map_iff ι hP hc'' hd'').symm)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_order_of_bridge

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
