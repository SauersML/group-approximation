import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveStepTurn
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-40: cell turns are forward steps of the curve

Lane gl-p07-40.  Certifies no printed sentence on its own.

Let `(x, y)` be consecutive in a rotation of `l = invDarts X ow`.  A **cell turn** at `y` is a
dart `g` of `ow` that follows `α y` on `G₁.darts` (or on `G₂.darts`).  By
`witnessStep_alpha_eq_of_cellTurn`, `g = α x`, so `(α y, α x)` is consecutive on the cell arc and
`(x, y)` is consecutive in `Ḡ₁ = invDarts X G₁.darts` (resp. `Ḡ₂`).

* `witnessStep_step_of_cellTurn₁`: `Ḡ₁` is the first block of `w`, so `x` comes before `y`.
* `witnessStep_step_of_cellTurn₂`, with `y ∉ Ḡ₁`: if `x ∈ Ḡ₁`, then `x` is in the first block
  and `y`, which lies in `w` by the step 1 label, is in a later block.  If `x ∉ Ḡ₁`, then both
  `x` and `y` pass the filter of the block `cellG2Word`, so they stay consecutive there.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section StepCell

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A turn along `G₁` is a forward step of the curve.** -/
theorem witnessStep_step_of_cellTurn₁ {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (h : (invDarts X ow).rotate n = s ++ x :: y :: t)
    {p q : List X.toCombMap.Dart} {g : X.toCombMap.Dart}
    (hG : G₁.darts = p ++ X.toCombMap.alpha y :: g :: q) (hg : g ∈ ow) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y := by
  have hgx := witnessStep_alpha_eq_of_cellTurn E h hG hg
  subst hgx
  have hbar : invDarts X G₁.darts = (q.map X.toCombMap.alpha).reverse ++ x :: y ::
      (p.map X.toCombMap.alpha).reverse :=
    witnessStep_map_reverse_adj X.toCombMap.alpha_involutive hG
  unfold WitnessCurveSublistList.StepNext
  refine Or.inl ⟨(q.map X.toCombMap.alpha).reverse, [],
    (p.map X.toCombMap.alpha).reverse ++ (FourBlock.sideAWord a b G₁ G₂ ++
      FourBlock.cellG2Word G₁ G₂ ++ FourBlock.sideBWord b G₁ G₂), ?_⟩
  rw [witnessStep_curve_eq_append]
  exact witnessStep_adj_append hbar

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStep_step_of_cellTurn₁

/-- **A turn along `G₂` into a dart off `Ḡ₁` is a forward step of the curve.** -/
theorem witnessStep_step_of_cellTurn₂ {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hlab : ∀ e ∈ invDarts X ow, e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
      X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (h : (invDarts X ow).rotate n = s ++ x :: y :: t)
    {p q : List X.toCombMap.Dart} {g : X.toCombMap.Dart}
    (hG : G₂.darts = p ++ X.toCombMap.alpha y :: g :: q) (hg : g ∈ ow)
    (hy1 : y ∉ invDarts X G₁.darts) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y := by
  have hgx := witnessStep_alpha_eq_of_cellTurn E h hG hg
  subst hgx
  have hbar : invDarts X G₂.darts = (q.map X.toCombMap.alpha).reverse ++ x :: y ::
      (p.map X.toCombMap.alpha).reverse :=
    witnessStep_map_reverse_adj X.toCombMap.alpha_involutive hG
  have hyl : y ∈ invDarts X ow := (List.mem_rotate (n := n)).mp (by rw [h]; simp)
  have hyw : y ∈ witnessSublistCurve a b G₁ G₂ := witnessSublist_mem_curve (hlab y hyl)
  unfold WitnessCurveSublistList.StepNext
  refine Or.inl ?_
  by_cases hx1 : x ∈ invDarts X G₁.darts
  · rw [witnessStep_curve_eq_append] at hyw ⊢
    have hyR : y ∈ FourBlock.sideAWord a b G₁ G₂ ++ FourBlock.cellG2Word G₁ G₂ ++
        FourBlock.sideBWord b G₁ G₂ := by
      rcases List.mem_append.mp hyw with hy | hy
      · exact absurd hy hy1
      · exact hy
    exact witnessStep_forward_of_mem_append hx1 hyR
  · have hx2 : x ∈ invDarts X G₂.darts := by
      rw [hbar]
      simp
    have hy2 : y ∈ invDarts X G₂.darts := by
      rw [hbar]
      simp
    have hC : ∃ u z : List X.toCombMap.Dart, FourBlock.cellG2Word G₁ G₂ = u ++ x :: y :: z := by
      unfold FourBlock.cellG2Word
      exact witnessStep_filter_adj hbar
        (List.mem_filter.mpr ⟨hx2, @decide_eq_true _ (_) ⟨hx1, hx2⟩⟩)
        (List.mem_filter.mpr ⟨hy2, @decide_eq_true _ (_) ⟨hy1, hy2⟩⟩)
    obtain ⟨u', z', huz⟩ := hC
    refine ⟨invDarts X G₁.darts ++ FourBlock.sideAWord a b G₁ G₂ ++ u', [],
      z' ++ FourBlock.sideBWord b G₁ G₂, ?_⟩
    unfold witnessSublistCurve
    exact witnessStep_adj_mid huz

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStep_step_of_cellTurn₂

end StepCell

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
