import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchJunction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBlockStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-52: list steps of the curve at a piece end

Lane gl-p07-52.  Certifies no printed sentence on its own.  NOT COMPILED.

The curve is `w = Ḡ₁ ++ Ā ++ Ḡ₂' ++ B̄` (`witnessSublistCurve`).
* `witnessStepPinch_nil_or_cons`: a list is empty or has a head.
* `witnessStepPinch_wrap`: if `y` heads `w`, then `(x, y)` is a wrap step.
* `witnessStepPinch_filter_head`: if `L` ends with `α y` and `y` passes a filter, then `y` heads
  the filtered inverse of `L`.
* `witnessStepPinch_mem_cellG2Word`: membership in `Ḡ₂'`.
* `witnessStepPinch_alpha_mem_of_head`: if `g = α x` heads `L`, then `α x ∈ L`.
* `witnessStepPinch_fwd_B`, `witnessStepPinch_fwd_G₂`, `witnessStepPinch_fwd_A`: forward steps
  of `w` into `B̄`, `Ḡ₂'` and `Ā` from an earlier block.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- A list is empty or has a head. -/
theorem witnessStepPinch_nil_or_cons {β : Type*} (L : List β) :
    L = [] ∨ ∃ (g : β) (r : List β), L = g :: r := by
  cases L with
  | nil => exact Or.inl rfl
  | cons g r => exact Or.inr ⟨g, r, rfl⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_nil_or_cons

/-- **A step onto the head of the word is a wrap step.** -/
theorem witnessStepPinch_wrap {β : Type*} {w l z : List β} {x y : β} (h : w = y :: z) :
    WitnessCurveSublistList.StepNext w l x y := by
  unfold WitnessCurveSublistList.StepNext
  exact Or.inr ⟨[], z, by simp [h], by simp⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_wrap

section PinchEndStep

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The filtered inverse of a list ending with `α y` starts with `y`**, when `y` passes. -/
theorem witnessStepPinch_filter_head {L p : List X.toCombMap.Dart} {y : X.toCombMap.Dart}
    (P : X.toCombMap.Dart → Bool) (hL : L = p ++ [X.toCombMap.alpha y])
    (hy : y ∈ (invDarts X L).filter P) : ∃ z : List X.toCombMap.Dart,
      (invDarts X L).filter P = y :: z := by
  have hinv : invDarts X L = y :: invDarts X p := by
    rw [hL, witnessStepPinch_invDarts_concat, X.toCombMap.alpha_involutive y]
  rw [hinv] at hy ⊢
  exact ⟨(invDarts X p).filter P, List.filter_cons_of_pos (List.mem_filter.mp hy).2⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_filter_head

/-- **Membership in the block `Ḡ₂'`.** -/
theorem witnessStepPinch_mem_cellG2Word {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {y : X.toCombMap.Dart} (hy1 : y ∉ invDarts X G₁.darts)
    (hy2 : y ∈ invDarts X G₂.darts) : y ∈ FourBlock.cellG2Word G₁ G₂ := by
  unfold FourBlock.cellG2Word
  exact List.mem_filter.mpr ⟨hy2, @decide_eq_true _ (_) ⟨hy1, hy2⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_mem_cellG2Word

/-- If `g = α x` heads `L`, then `α x ∈ L`. -/
theorem witnessStepPinch_alpha_mem_of_head {L r : List X.toCombMap.Dart}
    {g x : X.toCombMap.Dart} (hL : L = g :: r) (hgx : g = X.toCombMap.alpha x) :
    X.toCombMap.alpha x ∈ L := by
  rw [hL, ← hgx]
  simp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_alpha_mem_of_head

/-- **A forward step into `B̄`** from `Ḡ₁ ++ Ā ++ Ḡ₂'`. -/
theorem witnessStepPinch_fwd_B {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {l : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (hx : x ∈ invDarts X G₁.darts ++ FourBlock.sideAWord a b G₁ G₂ ++ FourBlock.cellG2Word G₁ G₂)
    (hy : y ∈ FourBlock.sideBWord b G₁ G₂) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) l x y := by
  unfold WitnessCurveSublistList.StepNext
  unfold witnessSublistCurve
  exact Or.inl (witnessStep_forward_of_mem_append hx hy)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_fwd_B

/-- **A forward step into `Ḡ₂'`** from `Ḡ₁ ++ Ā`. -/
theorem witnessStepPinch_fwd_G₂ {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {l : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (hx : x ∈ invDarts X G₁.darts ++ FourBlock.sideAWord a b G₁ G₂)
    (hy : y ∈ FourBlock.cellG2Word G₁ G₂) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) l x y := by
  unfold WitnessCurveSublistList.StepNext
  rw [witnessStepBlock_curve_eq_append₂]
  exact Or.inl (witnessStep_forward_of_mem_append hx (List.mem_append_left _ hy))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_fwd_G₂

/-- **A forward step into `Ā`** from `Ḡ₁`. -/
theorem witnessStepPinch_fwd_A {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {l : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (hx : x ∈ invDarts X G₁.darts) (hy : y ∈ FourBlock.sideAWord a b G₁ G₂) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) l x y := by
  unfold WitnessCurveSublistList.StepNext
  rw [witnessStep_curve_eq_append]
  exact Or.inl (witnessStep_forward_of_mem_append hx
    (List.mem_append_left _ (List.mem_append_left _ hy)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_fwd_A

end PinchEndStep

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
