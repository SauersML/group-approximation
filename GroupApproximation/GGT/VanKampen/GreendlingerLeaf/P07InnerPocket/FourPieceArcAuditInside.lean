import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcAuditProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-21c: the reading part from the corrected residual

`pocketFourPieceInside_of_arcAuditResidual` proves `PocketFourPieceInsideStatement`
(`FourPieceOffSplit.lean`) from the corrected residual `PocketFourPieceArcAuditResidualStatement`
(`FourPieceArcAuditStatement.lean`).  The helpers are in `FourPieceArcAuditProof.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Lane gl-p07-21c: the reading part from the corrected residual.** -/
theorem pocketFourPieceInside_of_arcAuditResidual
    (h : PocketFourPieceArcAuditResidualStatement.{u, w, v}) :
    PocketFourPieceInsideStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hout
    hinner houter C hC hCf hCa hCb
  obtain ⟨G₁, hG₁⟩ := h₁
  obtain ⟨G₂, hG₂⟩ := h₂
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
      houter C hC hCf hCa hCb with
    ⟨faces, outerWalk, E, hCF, hsub, hdart, hn1, hn2, hnb, hna, harc₁, hall₁, harc₂, hall₂⟩ |
      ⟨faces, outerWalk, _n, E, hCF, ⟨A, hA⟩ | ⟨A, hA⟩⟩
  rotate_left
  · exact ⟨faces, outerWalk, ArcAudit.inside_of_arc_left (a := a) (b := b) (K := K) E hCF A hA⟩
  · exact ⟨faces, outerWalk, ArcAudit.inside_of_arc_right (a := a) (b := b) (K := K) E hCF A hA⟩
  by_cases hx₁ : ∃ e ∈ invDarts X outerWalk, e ∉ invDarts X G₁.darts
  swap
  · obtain ⟨_n, A, hA⟩ :=
      hall₁ fun e he => Classical.byContradiction fun hn => hx₁ ⟨e, he, hn⟩
    exact ⟨faces, outerWalk, ArcAudit.inside_of_arc_left (a := a) (b := b) (K := K) E hCF A hA⟩
  by_cases hx₂ : ∃ e ∈ invDarts X outerWalk, e ∉ invDarts X G₂.darts
  swap
  · obtain ⟨_n, A, hA⟩ :=
      hall₂ fun e he => Classical.byContradiction fun hn => hx₂ ⟨e, he, hn⟩
    exact ⟨faces, outerWalk, ArcAudit.inside_of_arc_right (a := a) (b := b) (K := K) E hCF A hA⟩
  have hlabW : ∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts ∨
      e ∈ invDarts X G₂.darts ∨ X.toCombMap.alpha e ∈ a.sideFrom j ∨
        X.toCombMap.alpha e ∈ b.sideFrom i := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    rcases hdart d (List.mem_reverse.mp hd) with hd₁ | hd₂ | ⟨hK, ha, hb, hQ⟩
    · exact Or.inl hd₁
    · exact Or.inr (Or.inl hd₂)
    · exact PocketLabel.label_of_pocket hij hai hbi hfirst hsecond hG₁ hG₂ hw hQ hK ha hb
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
    (ArcAudit.exists_not_mem_right (P := fun e => e ∈ invDarts X G₁.darts) hm₁ hU₁ hx₁)
  obtain ⟨A₂, hA₂⟩ := harc₂ m₂ U₂ V₂ hm₂ hU₂
    (ArcAudit.exists_not_mem_right (P := fun e => e ∈ invDarts X G₂.darts) hm₂ hU₂ hx₂)
  obtain ⟨k, hk⟩ := SideBound.exists_rotate_invDarts outerWalk m
  refine ⟨faces, outerWalk, k, R₁, R₂, A₁, A₂, E, hCF, ?_, ?_, fun _ _ => hsub⟩
  · rw [hk, hrot, hA₁, hA₂]
  · rcases hcase with hc | ⟨hc, hc0⟩
    · exact Or.inl hc
    · refine Or.inr ⟨hc, ?_⟩
      rcases hc0 with h0 | h0
      · exact Or.inl (InputProof.length_eq_zero_of_invDarts_eq_nil A₁ (hA₁.symm.trans h0))
      · exact Or.inr (InputProof.length_eq_zero_of_invDarts_eq_nil A₂ (hA₂.symm.trans h0))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketFourPieceInside_of_arcAuditResidual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
