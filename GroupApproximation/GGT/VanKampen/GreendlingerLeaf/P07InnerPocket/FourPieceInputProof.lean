import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceInputProofStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabelDart
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBoundCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-20b: the reading part from the residual

`pocketFourPieceInside_of_inputProofResidual` proves `PocketFourPieceInsideStatement`
(`FourPieceOffSplit.lean`) from `PocketFourPieceInputProofResidualStatement`
(`FourPieceInputProofStatement.lean`).  The context is Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).

The steps:
* **Labels** by `PocketLabel.label_of_pocket`.
* **Four-piece order** by `FourPiece.exists_fourPiece`.
* **Blocks as prefixes** of rotations (`InputProof.exists_rotate_eq_append_of_mid`).
* **Arcs** by the residual's run clauses.
* **Rotation** by `SideBound.exists_rotate_invDarts`.
* **Zero-length arcs** from empty blocks (`InputProof.length_eq_zero_of_invDarts_eq_nil`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **A middle block of a rotation is a prefix of another rotation.** -/
theorem InputProof.exists_rotate_eq_append_of_mid {α : Type*} {l : List α} {n : ℕ}
    {R U S : List α} (h : l.rotate n = R ++ U ++ S) : ∃ (m : ℕ) (V : List α),
      l.rotate m = U ++ V := by
  refine ⟨n + R.length, S ++ R, ?_⟩
  rw [← List.rotate_rotate, h, List.append_assoc, List.rotate_append_length_eq,
    List.append_assoc]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.InputProof.exists_rotate_eq_append_of_mid

/-- **An arc with empty inverse darts has length zero.** -/
theorem InputProof.length_eq_zero_of_invDarts_eq_nil {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    {cycle : List X.toCombMap.Dart} (A : CyclicArc cycle) (h : invDarts X A.darts = []) :
    A.length = 0 := by
  rw [← CyclicArc.darts_length]
  have hlen := congrArg List.length h
  simpa [invDarts] using hlen

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.InputProof.length_eq_zero_of_invDarts_eq_nil

/-- **Lane gl-p07-20b: the reading part from the residual.**  See the module docstring. -/
theorem pocketFourPieceInside_of_inputProofResidual
    (h : PocketFourPieceInputProofResidualStatement.{u, w, v}) :
    PocketFourPieceInsideStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hout
    hinner houter C hC hCf hCa hCb
  obtain ⟨G₁, hG₁⟩ := h₁
  obtain ⟨G₂, hG₂⟩ := h₂
  obtain ⟨faces, outerWalk, E, hCF, hsub, hdart, hn1, hn2, hnb, hna, harc₁, harc₂⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter
      C hC hCf hCa hCb
  have hlabW : ∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts ∨
      e ∈ invDarts X G₂.darts ∨ X.toCombMap.alpha e ∈ a.sideFrom j ∨
        X.toCombMap.alpha e ∈ b.sideFrom i := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    obtain ⟨hK, ha, hb, hQ⟩ := hdart d (List.mem_reverse.mp hd)
    exact PocketLabel.label_of_pocket hij hai hbi hfirst hsecond hG₁ hG₂ hw hQ hK ha hb
  obtain ⟨m, R₁, U₁, R₂, U₂, hrot, hU₁, hU₂, hcase⟩ :=
    FourPiece.exists_fourPiece (P1 := fun e => e ∈ invDarts X G₁.darts)
      (P2 := fun e => e ∈ invDarts X G₂.darts)
      (Pa := fun e => X.toCombMap.alpha e ∈ a.sideFrom j)
      (Pb := fun e => X.toCombMap.alpha e ∈ b.sideFrom i) hlabW hn1 hn2 hnb hna
  have hrot₁ : (invDarts X outerWalk).rotate m = R₁ ++ U₁ ++ (R₂ ++ U₂) := by
    rw [hrot]
    simp only [List.append_assoc]
  have hrot₂ : (invDarts X outerWalk).rotate m = R₁ ++ U₁ ++ R₂ ++ U₂ ++ [] := by
    rw [hrot, List.append_nil]
  obtain ⟨m₁, V₁, hm₁⟩ := InputProof.exists_rotate_eq_append_of_mid hrot₁
  obtain ⟨m₂, V₂, hm₂⟩ := InputProof.exists_rotate_eq_append_of_mid hrot₂
  obtain ⟨A₁, hA₁⟩ := harc₁ m₁ U₁ V₁ hm₁ hU₁
  obtain ⟨A₂, hA₂⟩ := harc₂ m₂ U₂ V₂ hm₂ hU₂
  obtain ⟨k, hk⟩ := SideBound.exists_rotate_invDarts outerWalk m
  refine ⟨faces, outerWalk, k, R₁, R₂, A₁, A₂, E, hCF, ?_, ?_, fun _ _ => hsub⟩
  · rw [hk, hrot, hA₁, hA₂]
  · rcases hcase with hc | ⟨hc, hc0⟩
    · exact Or.inl hc
    · refine Or.inr ⟨hc, ?_⟩
      rcases hc0 with h0 | h0
      · exact Or.inl (InputProof.length_eq_zero_of_invDarts_eq_nil A₁ (hA₁.symm.trans h0))
      · exact Or.inr (InputProof.length_eq_zero_of_invDarts_eq_nil A₂ (hA₂.symm.trans h0))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketFourPieceInside_of_inputProofResidual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
