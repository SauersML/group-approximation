import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSkipStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSideWalk
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveStepTurn
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-51: a pair off every turn is a skip

Lane gl-p07-51.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepSkip_vertexOf_of_cellNext`, `witnessStepSkip_vertexOf_of_sideNext`,
  `witnessStepSkip_vertexOf_of_pieceNext`: the next dart `g` after `d` in a piece of the curve
  starts where `α d` starts.
* `witnessStepSkip_vertexOf_of_rotate`: for `(x, y)` consecutive in a rotation of
  `invDarts X ow`, `α x` starts at the vertex of `y`.
* `witnessStepSkip_eq_append_singleton`: a member with no successor is the last entry.
* `witnessStepSkip_curve_head`: if `α y` is the last dart of `G₁`, then `y` heads the curve word.
* `witnessStepSkip_skipAt`: a pair with no cell turn and no corner turn is a skip.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **A member with no successor is the last entry.** -/
theorem witnessStepSkip_eq_append_singleton {β : Type*} {L : List β} {d : β} (hd : d ∈ L)
    (hno : ∀ g : β, ¬ ∃ p q : List β, L = p ++ d :: g :: q) : ∃ p : List β, L = p ++ [d] := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem hd
  cases t with
  | nil => exact ⟨s, hst⟩
  | cons g q => exact (hno g ⟨s, q, hst⟩).elim

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSkip_eq_append_singleton

section SkipVertex

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A cell-arc successor starts where the reverse starts.** -/
theorem witnessStepSkip_vertexOf_of_cellNext {k : Fin X.rCellCount}
    (Γ : CyclicArc (cellDarts X k)) {p q : List X.toCombMap.Dart} {d g : X.toCombMap.Dart}
    (hG : Γ.darts = p ++ d :: g :: q) :
    X.toCombMap.vertexOf g = X.toCombMap.vertexOf (X.toCombMap.alpha d) := by
  have hchain : X.toCombMap.facePerm d = g :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp
      (PocketRun.arcDarts_isChain (X.faceBoundary (cell X k).face) Γ) hG
  rw [← hchain, PocketRun.facePerm_eq_sigma_alpha, X.toCombMap.vertexOf_sigma]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSkip_vertexOf_of_cellNext

/-- **A region-side successor starts where the reverse starts.** -/
theorem witnessStepSkip_vertexOf_of_sideNext (c : RegionCandidate D eps X)
    (k : Fin X.rCellCount) {p q : List X.toCombMap.Dart} {d g : X.toCombMap.Dart}
    (h : c.sideFrom k = p ++ d :: g :: q) :
    X.toCombMap.vertexOf g = X.toCombMap.vertexOf (X.toCombMap.alpha d) := by
  obtain ⟨m, -, hme, -⟩ :=
    witnessStepSide_sigma_of_boundaryStep (witnessStepSide_boundaryStep_of_side c k h)
  rw [← hme, PocketRun.vertexOf_sigma_pow]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSkip_vertexOf_of_sideNext

/-- **A piece successor starts where the reverse starts.** -/
theorem witnessStepSkip_vertexOf_of_pieceNext {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {d g : X.toCombMap.Dart} (h : WitnessStepSkipPieceNext a b G₁ G₂ d g) :
    X.toCombMap.vertexOf g = X.toCombMap.vertexOf (X.toCombMap.alpha d) := by
  unfold WitnessStepSkipPieceNext at h
  rcases h with ⟨p, q, h⟩ | ⟨p, q, h⟩ | ⟨p, q, h⟩ | ⟨p, q, h⟩
  · exact witnessStepSkip_vertexOf_of_cellNext G₁ h
  · exact witnessStepSkip_vertexOf_of_sideNext b i h
  · exact witnessStepSkip_vertexOf_of_cellNext G₂ h
  · exact witnessStepSkip_vertexOf_of_sideNext a j h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSkip_vertexOf_of_pieceNext

/-- **The next walk dart starts at the head of the previous one.**  For `(x, y)` consecutive in a
rotation of `invDarts X ow`, the walk has `α y` followed by `α x`, and `α x = σ^m (α (α y))`. -/
theorem witnessStepSkip_vertexOf_of_rotate {F : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow) {n : ℕ}
    {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (h : (invDarts X ow).rotate n = s ++ x :: y :: t) :
    X.toCombMap.vertexOf (X.toCombMap.alpha x) = X.toCombMap.vertexOf y := by
  have h0 : (ow.reverse.map X.toCombMap.alpha).rotate n = s ++ x :: y :: t := h
  have hr := witnessStep_rotate_of_rotate_inv X.toCombMap.alpha_involutive h0
  have hmem : X.toCombMap.alpha y ∈ ow := by
    have hrot : X.toCombMap.alpha y ∈ ow.rotate (ow.length - n % ow.length) := by
      rw [hr]
      simp
    exact List.mem_rotate.mp hrot
  obtain ⟨m, hm, hkeep, hfirst⟩ := PocketRun.exists_firstKeep ow hmem
  have hs := witnessStepSide_sigma_of_rotate E hr hm hkeep hfirst
  rw [← hs, PocketRun.vertexOf_sigma_pow, X.toCombMap.alpha_involutive y]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSkip_vertexOf_of_rotate

/-- **The last dart of `G₁`, reversed, heads the curve word.** -/
theorem witnessStepSkip_curve_head (a b : RegionCandidate D eps X)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    {p : List X.toCombMap.Dart} {y : X.toCombMap.Dart}
    (hG : G₁.darts = p ++ [X.toCombMap.alpha y]) :
    ∃ z : List X.toCombMap.Dart, witnessSublistCurve a b G₁ G₂ = y :: z := by
  have hinv : invDarts X (p ++ [X.toCombMap.alpha y]) = y :: invDarts X p := by
    simp only [Embedded.invDarts, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.map_cons, X.toCombMap.alpha_involutive y]
  refine ⟨invDarts X p ++ (FourBlock.sideAWord a b G₁ G₂ ++ FourBlock.cellG2Word G₁ G₂ ++
    FourBlock.sideBWord b G₁ G₂), ?_⟩
  rw [witnessStep_curve_eq_append, hG, hinv, List.cons_append]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSkip_curve_head

/-- **A pair off every cell and corner turn is a skip.**  Let `(x, y)` be consecutive in a
rotation of `invDarts X ow`, with no cell turn and no corner turn at `y`.  If the piece successor
`g` of `α y` were on `ow`, that would be a turn.  So `g` is off `ow`, and it starts at the vertex
of `y`, as `α x` does: a pinch.  If `α y` has no piece successor and lies on `G₁`, it is the last
dart of `G₁`, and `y` heads the curve word: a wrap-around corner turn.  Otherwise it is a piece
end. -/
theorem witnessStepSkip_skipAt {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (h : (invDarts X ow).rotate n = s ++ x :: y :: t)
    (hcell : ¬ WitnessStepCellTurn G₁ G₂ ow y)
    (hcorner : ¬ WitnessStepCornerTurn a b G₁ G₂ ow y) :
    WitnessStepSkipAt a b G₁ G₂ ow x y := by
  classical
  unfold WitnessStepCellTurn at hcell
  unfold WitnessStepCornerTurn at hcorner
  unfold WitnessStepSkipAt
  by_cases hex : ∃ g : X.toCombMap.Dart,
      WitnessStepSkipPieceNext a b G₁ G₂ (X.toCombMap.alpha y) g
  · obtain ⟨g, hg⟩ := hex
    by_cases hgo : g ∈ ow
    · exfalso
      unfold WitnessStepSkipPieceNext at hg
      rcases hg with ⟨p, q, hp⟩ | ⟨p, q, hp⟩ | ⟨p, q, hp⟩ | ⟨p, q, hp⟩
      · exact hcell (Or.inl ⟨p, q, g, hgo, hp⟩)
      · exact hcorner (Or.inl ⟨p, q, g, hgo, hp⟩)
      · exact hcorner (Or.inr (Or.inr (Or.inl ⟨p, q, g, hgo, hp⟩)))
      · exact hcorner (Or.inr (Or.inl ⟨p, q, g, hgo, hp⟩))
    · refine Or.inl ⟨g, hg, hgo, ?_⟩
      rw [witnessStepSkip_vertexOf_of_pieceNext hg, X.toCombMap.alpha_involutive y,
        witnessStepSkip_vertexOf_of_rotate E h]
  · by_cases hG : X.toCombMap.alpha y ∈ G₁.darts
    · exfalso
      have hno : ∀ g : X.toCombMap.Dart,
          ¬ ∃ p q : List X.toCombMap.Dart, G₁.darts = p ++ X.toCombMap.alpha y :: g :: q := by
        intro g hpq
        obtain ⟨p, q, hpq⟩ := hpq
        exact hex ⟨g, Or.inl ⟨p, q, hpq⟩⟩
      obtain ⟨p, hp⟩ := witnessStepSkip_eq_append_singleton hG hno
      obtain ⟨z, hz⟩ := witnessStepSkip_curve_head a b G₁ G₂ hp
      exact hcorner (Or.inr (Or.inr (Or.inr ⟨[], z, by rw [hz, List.nil_append],
        fun t ht => by simp at ht⟩)))
    · exact Or.inr ⟨hG, fun g hg => hex ⟨g, hg⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSkip_skipAt

end SkipVertex

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
