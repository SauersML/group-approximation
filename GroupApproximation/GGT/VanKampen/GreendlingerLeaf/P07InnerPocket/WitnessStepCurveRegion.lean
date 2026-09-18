import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCurveAssemble
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchRegion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSideWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-66: hop chains along cell arcs and region boundaries

Lane gl-p07-66.  Certifies no printed sentence on its own.  NOT COMPILED: authored without
running Lean.

Write `Hop' p q` for `witnessStepCurve_Hop M Γ (α p) q`.

Math.
* A face step `facePerm d = e` is `σ (α d) = e`, a hop with no intermediates.  So every infix
  of a cell arc is a `Hop'` chain (`witnessStepCurve_chain_of_arc`).
* A boundary step `d → e` of a face set `R` is `σ ^ m (α d) = e` with every intermediate dart
  having both faces in `R` (`witnessStepSide_sigma_of_boundaryStep`).  If no dart of `Γ` has
  both faces in `R` (**U1**), those intermediates and their reverses are off `Γ`.  So every infix
  of a rotation of a region boundary is a `Hop'` chain (`witnessStepCurve_chain_of_boundary`).
* U1 holds for a region `c` when each dart of `Γ` is on a side of `c` (a boundary dart, whose
  reverse is based off `c`) or is based off `c` (`witnessStepCurve_unique`).
* Duplicate-free bookkeeping: in a duplicate-free `l₁ ++ l₂ ++ l₃ ++ l₄`, an entry of `l₁` or
  `l₃` is in neither `l₂` nor `l₄`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **A face step is a hop.** -/
theorem witnessStepCurve_hop_of_facePerm {M : CombMap.{u}} {Γ : List M.Dart} {d e : M.Dart}
    (h : M.facePerm d = e) : witnessStepCurve_Hop M Γ (M.alpha d) e :=
  ⟨1, Nat.one_pos, by rw [pow_one, ← h, PocketRun.facePerm_eq_sigma_alpha],
    fun k hk hk1 => absurd hk1 (by omega)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_hop_of_facePerm

/-- An entry of the left part of a duplicate-free append is not in the right part. -/
theorem witnessStepCurve_nodup_left {β : Type*} {l₁ l₂ : List β} {x : β}
    (h : (l₁ ++ l₂).Nodup) (hx : x ∈ l₁) : x ∉ l₂ :=
  fun hx₂ => (List.nodup_append.mp h).2.2 x hx x hx₂ rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_nodup_left

/-- An entry of the right part of a duplicate-free append is not in the left part. -/
theorem witnessStepCurve_nodup_right {β : Type*} {l₁ l₂ : List β} {x : β}
    (h : (l₁ ++ l₂).Nodup) (hx : x ∈ l₂) : x ∉ l₁ :=
  fun hx₁ => (List.nodup_append.mp h).2.2 x hx₁ x hx rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_nodup_right

/-- **Three-block bookkeeping.**  An outer entry of a duplicate-free `l₁ ++ l₂ ++ l₃` is not in
the middle block. -/
theorem witnessStepCurve_nodup_three {β : Type*} {l₁ l₂ l₃ : List β} {x : β}
    (h : (l₁ ++ l₂ ++ l₃).Nodup) (hx : x ∈ l₁ ∨ x ∈ l₃) : x ∉ l₂ := by
  rcases hx with hx | hx
  · exact witnessStepCurve_nodup_left (h.sublist (List.sublist_append_left (l₁ ++ l₂) l₃)) hx
  · exact witnessStepCurve_nodup_right
      (h.sublist (List.Sublist.append (List.sublist_append_right l₁ l₂) (List.Sublist.refl l₃)))
      hx

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_nodup_three

/-- **Four-block bookkeeping.**  An entry of `l₁` or `l₃` of a duplicate-free
`l₁ ++ l₂ ++ l₃ ++ l₄` is in neither `l₂` nor `l₄`. -/
theorem witnessStepCurve_nodup_four {β : Type*} {l₁ l₂ l₃ l₄ : List β} {x : β}
    (h : (l₁ ++ l₂ ++ l₃ ++ l₄).Nodup) (hx : x ∈ l₁ ∨ x ∈ l₃) : x ∉ l₂ ∧ x ∉ l₄ := by
  have h₁₂ : l₁ ++ l₂ <+ l₁ ++ l₂ ++ l₃ ++ l₄ :=
    (List.sublist_append_left (l₁ ++ l₂) l₃).trans (List.sublist_append_left _ l₄)
  have h₁₄ : l₁ ++ l₄ <+ l₁ ++ l₂ ++ l₃ ++ l₄ :=
    List.Sublist.append ((List.sublist_append_left l₁ l₂).trans
      (List.sublist_append_left (l₁ ++ l₂) l₃)) (List.Sublist.refl l₄)
  have h₂₃ : l₂ ++ l₃ <+ l₁ ++ l₂ ++ l₃ ++ l₄ :=
    (List.Sublist.append (List.sublist_append_right l₁ l₂) (List.Sublist.refl l₃)).trans
      (List.sublist_append_left _ l₄)
  have h₃₄ : l₃ ++ l₄ <+ l₁ ++ l₂ ++ l₃ ++ l₄ :=
    List.Sublist.append (List.sublist_append_right (l₁ ++ l₂) l₃) (List.Sublist.refl l₄)
  rcases hx with hx | hx
  · exact ⟨witnessStepCurve_nodup_left (h.sublist h₁₂) hx,
      witnessStepCurve_nodup_left (h.sublist h₁₄) hx⟩
  · exact ⟨witnessStepCurve_nodup_right (h.sublist h₂₃) hx,
      witnessStepCurve_nodup_left (h.sublist h₃₄) hx⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_nodup_four

section Region

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}

/-- **A boundary step is a hop under U1.** -/
theorem witnessStepCurve_hop_of_boundaryStep {R : Finset X.toCombMap.Face}
    {Γ : List X.toCombMap.Dart}
    (hΓ : ∀ d ∈ Γ, X.toCombMap.faceOf d ∈ R → X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ R)
    {d e : X.toCombMap.Dart} (h : Embedded.BoundaryStep X R d e) :
    witnessStepCurve_Hop X.toCombMap Γ (X.toCombMap.alpha d) e := by
  obtain ⟨m, hm, he, hk⟩ := witnessStepSide_sigma_of_boundaryStep h
  refine ⟨m, hm, he, fun k h0 hkm => ⟨fun hmem => hΓ _ hmem (hk k h0 hkm).1 (hk k h0 hkm).2,
    fun hmem => ?_⟩⟩
  have h2 := hΓ _ hmem (hk k h0 hkm).2
  rw [X.toCombMap.alpha_involutive ((X.toCombMap.sigma ^ k) (X.toCombMap.alpha d))] at h2
  exact h2 (hk k h0 hkm).1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_hop_of_boundaryStep

/-- **An infix of a cell arc is a hop chain.** -/
theorem witnessStepCurve_chain_of_arc {Γ : List X.toCombMap.Dart} {k : Fin X.rCellCount}
    (A : CyclicArc (cellDarts X k)) {s l t : List X.toCombMap.Dart}
    (h : A.darts = s ++ l ++ t) :
    l.IsChain (fun p q => witnessStepCurve_Hop X.toCombMap Γ (X.toCombMap.alpha p) q) := by
  have hc : A.darts.IsChain fun d e => X.toCombMap.facePerm d = e :=
    PocketRun.arcDarts_isChain (X.faceBoundary (cell X k).face) A
  rw [h] at hc
  exact (hc.infix (List.infix_append s l t)).imp fun _ _ hr => witnessStepCurve_hop_of_facePerm hr

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_chain_of_arc

/-- **An infix of a rotation of a region boundary is a hop chain under U1.** -/
theorem witnessStepCurve_chain_of_boundary (c : RegionCandidate D eps X)
    {Γ : List X.toCombMap.Dart}
    (hΓ : ∀ d ∈ Γ, X.toCombMap.faceOf d ∈ c.1 → X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ c.1)
    {n : ℕ} {s l t : List X.toCombMap.Dart} (h : c.2.boundary.cycle.rotate n = s ++ l ++ t) :
    l.IsChain (fun p q => witnessStepCurve_Hop X.toCombMap Γ (X.toCombMap.alpha p) q) := by
  have hc : (c.2.boundary.cycle.rotate n).IsChain (Embedded.BoundaryStep X c.1) :=
    isChain_rotate_of_isChain_closes c.2.boundary.cycle_nonempty
      c.2.boundary.cycle_chain c.2.boundary.cycle_closes n
  rw [h] at hc
  exact (hc.infix (List.infix_append s l t)).imp fun _ _ hr =>
    witnessStepCurve_hop_of_boundaryStep hΓ hr

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_chain_of_boundary

/-- **U1 for a region.**  Darts of `Γ` on a side of `c` or based off `c` never have both faces
in `c`. -/
theorem witnessStepCurve_unique (c : RegionCandidate D eps X) (k : Fin X.rCellCount)
    {Γ : List X.toCombMap.Dart}
    (hΓ : ∀ d ∈ Γ, d ∈ c.sideFrom k ∨ X.toCombMap.faceOf d ∉ c.1) :
    ∀ d ∈ Γ, X.toCombMap.faceOf d ∈ c.1 → X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ c.1 := by
  intro d hd hf
  rcases hΓ d hd with hs | hn
  · exact ((c.2.boundary.cycle_mem_iff d).mp
      (CellPocketWalkColour.mem_boundary_of_mem_sideFrom c k hs)).2
  · exact absurd hf hn

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_unique

end Region

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
