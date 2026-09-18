import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSideWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-47: region-side turns are forward steps of the curve

Lane gl-p07-47.  Certifies no printed sentence on its own.

Let `(x, y)` be consecutive in a rotation of `l = invDarts X ow`.  A **side turn** at `y` is a
dart `g` of `ow` that follows `α y` on a region side.  The witness faces are off that region, so
by `witnessStepSide_alpha_eq_of_sideTurn` we get `g = α x`.  So `(x, y)` is consecutive in the
inverse side.

* `witnessStepSide_step_of_turnB`: the side `b.sideFrom i`, with `y` in the block `B̄`
  (`sideBWord`).  If `x ∈ B̄` as well, both pass the filter and stay consecutive.  Otherwise `x`
  is in the curve by the step 1 label, off the last block, and so before `y`.
* `witnessStepSide_step_of_turnA`: the side `a.sideFrom j`, with `y` in the block `Ā`
  (`sideAWord`), `α g ∉ Ḡ₂` and `g ∉ b.sideFrom i`.  If `x ∈ Ḡ₁`, it lies in the first block.
  Otherwise `x` passes the filter of `Ā` and stays consecutive with `y` there.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section SideStep

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A turn along `b.sideFrom i` into the block `B̄` is a forward step of the curve.** -/
theorem witnessStepSide_step_of_turnB {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F)
    (hlab : ∀ e ∈ invDarts X ow, e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
      X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i)
    (hR : ∀ f ∈ F, f ∉ b.1)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (h : (invDarts X ow).rotate n = s ++ x :: y :: t)
    {p q : List X.toCombMap.Dart} {g : X.toCombMap.Dart}
    (hS : b.sideFrom i = p ++ X.toCombMap.alpha y :: g :: q) (hg : g ∈ ow)
    (hyB : y ∈ FourBlock.sideBWord b G₁ G₂) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y := by
  have hgx := witnessStepSide_alpha_eq_of_sideTurn E hnb hR h hS hg
  subst hgx
  have hbar : invDarts X (b.sideFrom i) = (q.map X.toCombMap.alpha).reverse ++ x :: y ::
      (p.map X.toCombMap.alpha).reverse :=
    witnessStep_map_reverse_adj X.toCombMap.alpha_involutive hS
  have hxl : x ∈ invDarts X ow := (List.mem_rotate (n := n)).mp (by rw [h]; simp)
  have hxw : x ∈ witnessSublistCurve a b G₁ G₂ := witnessSublist_mem_curve (hlab x hxl)
  unfold WitnessCurveSublistList.StepNext
  refine Or.inl ?_
  by_cases hxB : x ∈ FourBlock.sideBWord b G₁ G₂
  · have hC : ∃ u z : List X.toCombMap.Dart,
        FourBlock.sideBWord b G₁ G₂ = u ++ x :: y :: z := by
      unfold FourBlock.sideBWord at hxB hyB ⊢
      exact witnessStep_filter_adj hbar hxB hyB
    obtain ⟨u', z', huz⟩ := hC
    refine ⟨invDarts X G₁.darts ++ FourBlock.sideAWord a b G₁ G₂ ++
      FourBlock.cellG2Word G₁ G₂ ++ u', [], z', ?_⟩
    unfold witnessSublistCurve
    rw [huz]
    simp
  · have hxL : x ∈ invDarts X G₁.darts ++ FourBlock.sideAWord a b G₁ G₂ ++
        FourBlock.cellG2Word G₁ G₂ := by
      unfold witnessSublistCurve at hxw
      rcases List.mem_append.mp hxw with hx | hx
      · exact hx
      · exact absurd hx hxB
    unfold witnessSublistCurve
    exact witnessStep_forward_of_mem_append hxL hyB

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSide_step_of_turnB

/-- **A turn along `a.sideFrom j` into the block `Ā` is a forward step of the curve**, when the
turned-to dart `g` has `α g ∉ Ḡ₂` and `g ∉ b.sideFrom i`. -/
theorem witnessStepSide_step_of_turnA {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F)
    (hR : ∀ f ∈ F, f ∉ a.1)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (h : (invDarts X ow).rotate n = s ++ x :: y :: t)
    {p q : List X.toCombMap.Dart} {g : X.toCombMap.Dart}
    (hS : a.sideFrom j = p ++ X.toCombMap.alpha y :: g :: q) (hg : g ∈ ow)
    (hyA : y ∈ FourBlock.sideAWord a b G₁ G₂)
    (hg2 : X.toCombMap.alpha g ∉ invDarts X G₂.darts) (hgb : g ∉ b.sideFrom i) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y := by
  have hgx := witnessStepSide_alpha_eq_of_sideTurn E hnb hR h hS hg
  subst hgx
  rw [X.toCombMap.alpha_involutive x] at hg2
  have hbar : invDarts X (a.sideFrom j) = (q.map X.toCombMap.alpha).reverse ++ x :: y ::
      (p.map X.toCombMap.alpha).reverse :=
    witnessStep_map_reverse_adj X.toCombMap.alpha_involutive hS
  unfold WitnessCurveSublistList.StepNext
  refine Or.inl ?_
  by_cases hx1 : x ∈ invDarts X G₁.darts
  · rw [witnessStep_curve_eq_append]
    have hyR : y ∈ FourBlock.sideAWord a b G₁ G₂ ++ FourBlock.cellG2Word G₁ G₂ ++
        FourBlock.sideBWord b G₁ G₂ :=
      List.mem_append_left _ (List.mem_append_left _ hyA)
    exact witnessStep_forward_of_mem_append hx1 hyR
  · have hxa : x ∈ invDarts X (a.sideFrom j) := by
      rw [hbar]
      simp
    have hC : ∃ u z : List X.toCombMap.Dart,
        FourBlock.sideAWord a b G₁ G₂ = u ++ x :: y :: z := by
      unfold FourBlock.sideAWord at hyA ⊢
      exact witnessStep_filter_adj hbar
        (List.mem_filter.mpr ⟨hxa, @decide_eq_true _ (_) ⟨hx1, hg2, hgb⟩⟩) hyA
    obtain ⟨u', z', huz⟩ := hC
    refine ⟨invDarts X G₁.darts ++ u', [],
      z' ++ FourBlock.cellG2Word G₁ G₂ ++ FourBlock.sideBWord b G₁ G₂, ?_⟩
    unfold witnessSublistCurve
    rw [huz]
    simp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSide_step_of_turnA

end SideStep

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
