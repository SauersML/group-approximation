import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchCutStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerFace
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-54: the off-lobe pinch residual from the prefix residual

Lane gl-p07-54.  Certifies no printed sentence on its own.  NOT COMPILED.

`witnessStepPinchCut_pinchOff_of_pinchCut` proves `WitnessStepPinchOffStatement` from
`WitnessStepPinchCutStatement`.  The backward disjunct passes through unchanged.  In the forward
disjunct:
* `x` and `y` are distinct entries of the curve (`witnessStepPinchCut_stepNext`);
* if `x` comes first, `StepNext` holds by its first clause;
* if `y` comes first, the residual puts the curve prefix before `y` off the witness faces, so off
  `invDarts X ow`, and `StepNext` holds by its wrap-around clause.

See `WitnessStepPinchCutStatement.lean` for the truth check and the LOUD notes.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Two distinct entries of a list come in one order or the other.** -/
theorem witnessStepPinchCut_order {β : Type*} {L : List β} {x y : β} (hx : x ∈ L) (hy : y ∈ L)
    (hxy : x ≠ y) : (∃ p m z : List β, L = p ++ x :: (m ++ y :: z)) ∨
      ∃ p m z : List β, L = p ++ y :: (m ++ x :: z) := by
  induction L with
  | nil => simp at hx
  | cons c L ih =>
    rcases List.mem_cons.mp hx with hxc | hx'
    · have hy' : y ∈ L := (List.mem_cons.mp hy).resolve_left (fun h => hxy (hxc.trans h.symm))
      obtain ⟨m, z, hmz⟩ := List.append_of_mem hy'
      exact Or.inl ⟨[], m, z, by simp [hxc, hmz]⟩
    · rcases List.mem_cons.mp hy with hyc | hy'
      · obtain ⟨m, z, hmz⟩ := List.append_of_mem hx'
        exact Or.inr ⟨[], m, z, by simp [hyc, hmz]⟩
      · rcases ih hx' hy' with ⟨p, m, z, h⟩ | ⟨p, m, z, h⟩
        · exact Or.inl ⟨c :: p, m, z, by simp [h]⟩
        · exact Or.inr ⟨c :: p, m, z, by simp [h]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchCut_order

section PinchCut

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The witness step from the prefix fact.**  For a consecutive pair `(x, y)` of the inverted
enclosing walk, `StepNext` holds on the curve as soon as the curve prefix before `y` lies off the
witness faces whenever `y` comes before `x`. -/
theorem witnessStepPinchCut_stepNext {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X (witnessFaces a b K c) ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K c)
    (hlab : ∀ e ∈ invDarts X ow, e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
      X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (hr : (invDarts X ow).rotate n = s ++ x :: y :: t)
    (hface : ∀ pre mid post : List X.toCombMap.Dart,
      witnessSublistCurve a b G₁ G₂ = pre ++ y :: (mid ++ x :: post) →
      ∀ e ∈ pre, X.toCombMap.faceOf e ∉ witnessFaces a b K c) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y := by
  have hl : (invDarts X ow).Nodup :=
    (List.nodup_reverse.mpr E.nodup).map X.toCombMap.alpha.injective
  have hrn : (s ++ x :: y :: t).Nodup := by
    rw [← hr]
    exact List.nodup_rotate.mpr hl
  have h2 : (x :: y :: t).Nodup :=
    List.Nodup.sublist (List.sublist_append_right s (x :: y :: t)) hrn
  have hxy : x ≠ y := by
    intro hxy
    exact (List.nodup_cons.mp h2).1 (by simp [hxy])
  have hx : x ∈ invDarts X ow := by
    have h : x ∈ (invDarts X ow).rotate n := by
      rw [hr]
      simp
    exact List.mem_rotate.mp h
  have hy : y ∈ invDarts X ow := by
    have h : y ∈ (invDarts X ow).rotate n := by
      rw [hr]
      simp
    exact List.mem_rotate.mp h
  rcases witnessStepPinchCut_order (witnessSublist_mem_curve (a := a) (b := b) (G₁ := G₁)
      (G₂ := G₂) (hlab x hx)) (witnessSublist_mem_curve (a := a) (b := b) (G₁ := G₁)
      (G₂ := G₂) (hlab y hy)) hxy with ⟨pre, mid, post, hw⟩ | ⟨pre, mid, post, hw⟩
  · exact Or.inl ⟨pre, mid, post, hw⟩
  · refine Or.inr ⟨pre, mid ++ x :: post, hw, fun e he hel => ?_⟩
    have hF := hnb _ (witnessStepCorner_alpha_mem_of_mem_invDarts hel)
    rw [X.toCombMap.alpha_involutive e] at hF
    exact hface pre mid post hw e he hF

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchCut_stepNext

end PinchCut

/-- **Lane gl-p07-54: the off-lobe pinch residual from the prefix residual.** -/
theorem witnessStepPinchCut_pinchOff_of_pinchCut (h : WitnessStepPinchCutStatement.{u, w, v}) :
    WitnessStepPinchOffStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun n s t x y hr hcell hside hblock hcorner hpinch => ?_
    exact witnessStepPinchCut_stepNext E hnb hlab hr
      (hfwd n s t x y hr hcell hside hblock hcorner hpinch)
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchCut_pinchOff_of_pinchCut

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
