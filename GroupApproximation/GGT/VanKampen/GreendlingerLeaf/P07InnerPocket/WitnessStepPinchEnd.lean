import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchEndStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-52: the piece-end case of a skip

Lane gl-p07-52.  Certifies no printed sentence on its own.  NOT COMPILED.

Let `(x, y)` be consecutive on the inverse outside walk, with `α y` the last dart of a piece `P`
of `Γ = G₁ · B · G₂ · A` other than `G₁`.  Let `g` be the first dart of the next nonempty piece.
* If all pieces after `P` up to and including `G₁` are empty, then `y` heads the curve
  `w = Ḡ₁ ++ Ā ++ Ḡ₂' ++ B̄`, and `(x, y)` is a wrap step.
* Otherwise the junction fan from `α (α y)` to `g` (`WitnessStepPinchJunction.lean`) gives either
  `g = α x`, and then `x` lies in an earlier block of `w`, which is a forward step, or a pinch
  across the junction (`WitnessStepPinchAt`).
The three cases are `witnessStepPinch_step_of_end_A` (`P = A`), `witnessStepPinch_step_of_end_G₂`
(`P = G₂`) and `witnessStepPinch_step_of_end_B` (`P = B`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section PinchEnd

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Piece end in `A`.** -/
theorem witnessStepPinch_step_of_end_A {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (hr : (invDarts X ow).rotate n = s ++ x :: y :: t)
    (hFa : ∀ f ∈ F, f ∉ a.1) (hFi : (cell X i).face ∉ F) (hij : i ≠ j) (hai : a.JoinsCells i j)
    (hai₁ : 0 < (a.cellArcList i).length) (K₁ : CyclicArc (cellDarts X i))
    (hK₁ : K₁.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    {p : List X.toCombMap.Dart} (hS : a.sideFrom j = p ++ [X.toCombMap.alpha y])
    (hyA : y ∈ FourBlock.sideAWord a b G₁ G₂) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y ∨
      WitnessStepPinchAt a b G₁ G₂ ow x y := by
  rcases witnessStepPinch_nil_or_cons G₁.darts with hG1 | ⟨g, r, hG1⟩
  · obtain ⟨z, hz⟩ : ∃ z : List X.toCombMap.Dart, FourBlock.sideAWord a b G₁ G₂ = y :: z := by
      unfold FourBlock.sideAWord at hyA ⊢
      exact witnessStepPinch_filter_head _ hS hyA
    have h1 : invDarts X G₁.darts = [] := by simp [Embedded.invDarts, hG1]
    exact Or.inl (witnessStepPinch_wrap
      (z := z ++ FourBlock.cellG2Word G₁ G₂ ++ FourBlock.sideBWord b G₁ G₂)
      (by simp [witnessSublistCurve, h1, hz]))
  · exact witnessStepPinch_step_or_pinch_of_fan E hnb hr
      (witnessStepPinch_junction_A_G₁ hFa hFi hij hai hai₁ K₁ hK₁ hS hG1)
      (Or.inr (Or.inr ⟨⟨p, hS⟩, r, hG1⟩))
      (fun hgx => witnessStepPinch_fwd_A (witnessStepCorner_mem_invDarts_of_alpha_mem
        (witnessStepPinch_alpha_mem_of_head hG1 hgx)) hyA)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_step_of_end_A

/-- **Piece end in `G₂`.** -/
theorem witnessStepPinch_step_of_end_G₂ {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (hr : (invDarts X ow).rotate n = s ++ x :: y :: t)
    (hFa : ∀ f ∈ F, f ∉ a.1) (hFi : (cell X i).face ∉ F) (hFj : (cell X j).face ∉ F)
    (hij : i ≠ j) (hab : Disjoint a.1 b.1) (hai : a.JoinsCells i j)
    (hai₁ : 0 < (a.cellArcList i).length) (haj₁ : 0 < (a.cellArcList j).length)
    (hcai : (cell X i).face ∉ a.1) (hcaj : (cell X j).face ∉ a.1)
    (K₁ : CyclicArc (cellDarts X i))
    (hK₁ : K₁.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (K₂ : CyclicArc (cellDarts X j))
    (hK₂ : K₂.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {p : List X.toCombMap.Dart} (hG : G₂.darts = p ++ [X.toCombMap.alpha y])
    (hyC : y ∈ FourBlock.cellG2Word G₁ G₂) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y ∨
      WitnessStepPinchAt a b G₁ G₂ ow x y := by
  rcases witnessStepPinch_nil_or_cons (a.sideFrom j) with hA | ⟨g, r, hA⟩
  · rcases witnessStepPinch_nil_or_cons G₁.darts with hG1 | ⟨g, r, hG1⟩
    · obtain ⟨z, hz⟩ : ∃ z : List X.toCombMap.Dart, FourBlock.cellG2Word G₁ G₂ = y :: z := by
        unfold FourBlock.cellG2Word at hyC ⊢
        exact witnessStepPinch_filter_head _ hG hyC
      have h1 : invDarts X G₁.darts = [] := by simp [Embedded.invDarts, hG1]
      have h2 : FourBlock.sideAWord a b G₁ G₂ = [] := by
        simp [FourBlock.sideAWord, hA, Embedded.invDarts]
      exact Or.inl (witnessStepPinch_wrap (z := z ++ FourBlock.sideBWord b G₁ G₂)
        (by simp [witnessSublistCurve, h1, h2, hz]))
    · exact witnessStepPinch_step_or_pinch_of_fan E hnb hr
        (witnessStepPinch_junction_G₂_G₁ hFa hFi hFj hij hai hai₁ haj₁ K₁ hK₁ K₂ hK₂ hG hA hG1)
        (Or.inr (Or.inl ⟨⟨p, hG⟩, Or.inr ⟨hA, r, hG1⟩⟩))
        (fun hgx => witnessStepPinch_fwd_G₂ (List.mem_append_left _
          (witnessStepCorner_mem_invDarts_of_alpha_mem
            (witnessStepPinch_alpha_mem_of_head hG1 hgx))) hyC)
  · exact witnessStepPinch_step_or_pinch_of_fan E hnb hr
      (witnessStepPinch_junction_G₂_A hFa hFj hij hai haj₁ K₂ hK₂ hG hA)
      (Or.inr (Or.inl ⟨⟨p, hG⟩, Or.inl ⟨r, hA⟩⟩))
      (fun hgx => witnessStepPinch_fwd_G₂ (List.mem_append_right _
        (witnessStepCorner_mem_sideAWord hab (witnessStepPinch_alpha_mem_of_head hA hgx)
          hcai hcaj)) hyC)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_step_of_end_G₂

/-- **Piece end in `B`.** -/
theorem witnessStepPinch_step_of_end_B {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (hr : (invDarts X ow).rotate n = s ++ x :: y :: t)
    (hFa : ∀ f ∈ F, f ∉ a.1) (hFb : ∀ f ∈ F, f ∉ b.1) (hFi : (cell X i).face ∉ F)
    (hFj : (cell X j).face ∉ F) (hij : i ≠ j) (hab : Disjoint a.1 b.1)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) (hai₁ : 0 < (a.cellArcList i).length)
    (haj₁ : 0 < (a.cellArcList j).length) (hbj₁ : 0 < (b.cellArcList j).length)
    (hcai : (cell X i).face ∉ a.1) (hcaj : (cell X j).face ∉ a.1)
    (K₁ : CyclicArc (cellDarts X i))
    (hK₁ : K₁.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (K₂ : CyclicArc (cellDarts X j))
    (hK₂ : K₂.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {p : List X.toCombMap.Dart} (hS : b.sideFrom i = p ++ [X.toCombMap.alpha y])
    (hyB : y ∈ FourBlock.sideBWord b G₁ G₂) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y ∨
      WitnessStepPinchAt a b G₁ G₂ ow x y := by
  rcases witnessStepPinch_nil_or_cons G₂.darts with hG | ⟨g, r, hG⟩
  · rcases witnessStepPinch_nil_or_cons (a.sideFrom j) with hA | ⟨g, r, hA⟩
    · rcases witnessStepPinch_nil_or_cons G₁.darts with hG1 | ⟨g, r, hG1⟩
      · obtain ⟨z, hz⟩ : ∃ z : List X.toCombMap.Dart, FourBlock.sideBWord b G₁ G₂ = y :: z := by
          unfold FourBlock.sideBWord at hyB ⊢
          exact witnessStepPinch_filter_head _ hS hyB
        have h1 : invDarts X G₁.darts = [] := by simp [Embedded.invDarts, hG1]
        have h2 : FourBlock.sideAWord a b G₁ G₂ = [] := by
          simp [FourBlock.sideAWord, hA, Embedded.invDarts]
        have h3 : FourBlock.cellG2Word G₁ G₂ = [] := by
          simp [FourBlock.cellG2Word, hG, Embedded.invDarts]
        exact Or.inl (witnessStepPinch_wrap (z := z)
          (by simp [witnessSublistCurve, h1, h2, h3, hz]))
      · exact witnessStepPinch_step_or_pinch_of_fan E hnb hr
          (witnessStepPinch_junction_B_G₁ hFa hFb hFi hFj hij hai hbi hai₁ haj₁ hbj₁ K₁ hK₁ K₂
            hK₂ hS hG hA hG1)
          (Or.inl ⟨⟨p, hS⟩, Or.inr ⟨hG, Or.inr ⟨hA, r, hG1⟩⟩⟩)
          (fun hgx => witnessStepPinch_fwd_B (List.mem_append_left _ (List.mem_append_left _
            (witnessStepCorner_mem_invDarts_of_alpha_mem
              (witnessStepPinch_alpha_mem_of_head hG1 hgx)))) hyB)
    · exact witnessStepPinch_step_or_pinch_of_fan E hnb hr
        (witnessStepPinch_junction_B_A hFa hFb hFj hij hai hbi haj₁ hbj₁ K₂ hK₂ hS hG hA)
        (Or.inl ⟨⟨p, hS⟩, Or.inr ⟨hG, Or.inl ⟨r, hA⟩⟩⟩)
        (fun hgx => witnessStepPinch_fwd_B (List.mem_append_left _ (List.mem_append_right _
          (witnessStepCorner_mem_sideAWord hab (witnessStepPinch_alpha_mem_of_head hA hgx)
            hcai hcaj))) hyB)
  · exact witnessStepPinch_step_or_pinch_of_fan E hnb hr
      (witnessStepPinch_junction_B_G₂ hFb hFj hij hbi hbj₁ K₂ hK₂ hS hG)
      (Or.inl ⟨⟨p, hS⟩, Or.inl ⟨r, hG⟩⟩)
      (fun hgx => witnessStepPinch_fwd_B (List.mem_append_right _
        (witnessStepPinch_mem_cellG2Word
          (witnessStepCorner_not_mem_invG₁_of_mem_G₂ hij
            (witnessStepPinch_alpha_mem_of_head hG hgx))
          (witnessStepCorner_mem_invDarts_of_alpha_mem
            (witnessStepPinch_alpha_mem_of_head hG hgx)))) hyB)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_step_of_end_B

end PinchEnd

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
