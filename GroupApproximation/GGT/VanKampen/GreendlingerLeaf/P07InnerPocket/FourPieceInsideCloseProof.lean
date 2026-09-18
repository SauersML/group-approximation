import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceInsideCloseStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcAuditInside
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-45: the reading part from the lake-only side clause

* `fourPieceInsideClose_residual_of_arcAuditResidual`: `PocketFourPieceArcAuditResidualStatement`
  gives `FourPieceInsideCloseResidualStatement` (`FourPieceInsideCloseStatement.lean`).
* `fourPieceInsideClose_of_residual`: that residual gives `PocketFourPieceInsideStatement`.

The proof is `pocketFourPieceInside_of_arcAuditResidual` with two changes.
* The four-piece order runs with the labels `Pa' e := α e ∈ a.sideFrom j ∧ e ∉ Ḡ₁ ∧ e ∉ Ḡ₂` and
  `Pb' e := α e ∈ b.sideFrom i ∧ e ∉ Ḡ₁ ∧ e ∉ Ḡ₂`.  The two class hypotheses that mention `Pb'`
  are pointwise equivalent to the old ones (`fourPieceInsideClose_iff_b`, `_iff_a`).
* With both arcs empty, both `G`-runs are empty, so every entry of the cyclic word lies in
  `R₁ ++ R₂` and avoids `Ḡ₁` and `Ḡ₂`.  The lake-only side clause then gives
  `faces ⊆ sideFaces K.walk`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Pointwise equivalent classes have the same non-interleaving.** -/
theorem fourPieceInsideClose_noInterleave_congr {α : Type*} {A B : α → Prop} {l : List α}
    (hB : FourPiece.CyclicNoInterleave B l) (h : ∀ x, A x ↔ B x) :
    FourPiece.CyclicNoInterleave A l := by
  have hAB : A = B := funext fun x => propext (h x)
  rw [hAB]
  exact hB

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInsideClose_noInterleave_congr

/-- **The `b`-class with the primed label.** -/
theorem fourPieceInsideClose_iff_b {p1 p2 pb : Prop} :
    (p1 ∨ (¬ p2 ∧ (pb ∧ ¬ p1 ∧ ¬ p2))) ↔ (p1 ∨ (¬ p2 ∧ pb)) := by
  tauto

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInsideClose_iff_b

/-- **The `a`-class with the primed label.** -/
theorem fourPieceInsideClose_iff_a {p1 p2 pb : Prop} :
    (p1 ∨ (¬ p2 ∧ ¬ (pb ∧ ¬ p1 ∧ ¬ p2))) ↔ (p1 ∨ (¬ p2 ∧ ¬ pb)) := by
  tauto

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInsideClose_iff_a

/-- **An entry of `R₁ ++ R₂` carries `Pa` or `Pb`**, in either case of the four-piece order. -/
theorem fourPieceInsideClose_mem_of_case {α : Type*} {Pa Pb : α → Prop} {R₁ R₂ : List α}
    {Q : Prop}
    (h : (((∀ x ∈ R₁, Pa x) ∨ ∀ x ∈ R₁, Pb x) ∧ ((∀ x ∈ R₂, Pa x) ∨ ∀ x ∈ R₂, Pb x)) ∨
      ((∀ x ∈ R₁ ++ R₂, Pa x ∨ Pb x) ∧ Q)) {x : α} (hx : x ∈ R₁ ++ R₂) : Pa x ∨ Pb x := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h, _⟩
  · rcases List.mem_append.mp hx with hx | hx
    · rcases h₁ with h₁ | h₁
      · exact Or.inl (h₁ x hx)
      · exact Or.inr (h₁ x hx)
    · rcases h₂ with h₂ | h₂
      · exact Or.inl (h₂ x hx)
      · exact Or.inr (h₂ x hx)
  · exact h x hx

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInsideClose_mem_of_case

/-- **An arc of length zero has empty inverse darts.** -/
theorem fourPieceInsideClose_invDarts_eq_nil {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    {cycle : List X.toCombMap.Dart} (A : CyclicArc cycle) (h : A.length = 0) :
    invDarts X A.darts = [] := by
  have hd : A.darts = [] :=
    List.eq_nil_of_length_eq_zero (by rw [CyclicArc.darts_length]; exact h)
  rw [hd]
  simp [invDarts]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInsideClose_invDarts_eq_nil

/-- **The arc-audit residual gives the lake-only residual.**  Clause 3 only gains a hypothesis. -/
theorem fourPieceInsideClose_residual_of_arcAuditResidual
    (h : PocketFourPieceArcAuditResidualStatement.{u, w, v}) :
    FourPieceInsideCloseResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
      houter C hC hCf hCa hCb with
    ⟨faces, outerWalk, E, hCF, hsub, hrest⟩ | hbr
  · exact Or.inl ⟨faces, outerWalk, E, hCF, fun _ => hsub, hrest⟩
  · exact Or.inr hbr

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInsideClose_residual_of_arcAuditResidual

/-- **Lane gl-p07-45: the reading part from the lake-only residual.**  See the module docstring. -/
theorem fourPieceInsideClose_of_residual
    (h : FourPieceInsideCloseResidualStatement.{u, w, v}) :
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
  have hlab₀ : ∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts ∨
      e ∈ invDarts X G₂.darts ∨ X.toCombMap.alpha e ∈ a.sideFrom j ∨
        X.toCombMap.alpha e ∈ b.sideFrom i := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    rcases hdart d (List.mem_reverse.mp hd) with hd₁ | hd₂ | ⟨hK, ha, hb, hQ⟩
    · exact Or.inl hd₁
    · exact Or.inr (Or.inl hd₂)
    · exact PocketLabel.label_of_pocket hij hai hbi hfirst hsecond hG₁ hG₂ hw hQ hK ha hb
  have hlabW : ∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts ∨
      e ∈ invDarts X G₂.darts ∨
        (X.toCombMap.alpha e ∈ a.sideFrom j ∧ e ∉ invDarts X G₁.darts ∧
          e ∉ invDarts X G₂.darts) ∨
        (X.toCombMap.alpha e ∈ b.sideFrom i ∧ e ∉ invDarts X G₁.darts ∧
          e ∉ invDarts X G₂.darts) := by
    intro e he
    by_cases hg₁ : e ∈ invDarts X G₁.darts
    · exact Or.inl hg₁
    by_cases hg₂ : e ∈ invDarts X G₂.darts
    · exact Or.inr (Or.inl hg₂)
    rcases hlab₀ e he with hl | hl | hl | hl
    · exact absurd hl hg₁
    · exact absurd hl hg₂
    · exact Or.inr (Or.inr (Or.inl ⟨hl, hg₁, hg₂⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hl, hg₁, hg₂⟩))
  have hnb' : FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
      (¬ e ∈ invDarts X G₂.darts ∧ (X.toCombMap.alpha e ∈ b.sideFrom i ∧
        ¬ e ∈ invDarts X G₁.darts ∧ ¬ e ∈ invDarts X G₂.darts)))
      (invDarts X outerWalk) :=
    fourPieceInsideClose_noInterleave_congr hnb fun _ => fourPieceInsideClose_iff_b
  have hna' : FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
      (¬ e ∈ invDarts X G₂.darts ∧ ¬ (X.toCombMap.alpha e ∈ b.sideFrom i ∧
        ¬ e ∈ invDarts X G₁.darts ∧ ¬ e ∈ invDarts X G₂.darts)))
      (invDarts X outerWalk) :=
    fourPieceInsideClose_noInterleave_congr hna fun _ => fourPieceInsideClose_iff_a
  obtain ⟨m, R₁, U₁, R₂, U₂, hrot, hU₁, hU₂, hcase⟩ :=
    FourPiece.exists_fourPiece (P1 := fun e => e ∈ invDarts X G₁.darts)
      (P2 := fun e => e ∈ invDarts X G₂.darts)
      (Pa := fun e => X.toCombMap.alpha e ∈ a.sideFrom j ∧ ¬ e ∈ invDarts X G₁.darts ∧
        ¬ e ∈ invDarts X G₂.darts)
      (Pb := fun e => X.toCombMap.alpha e ∈ b.sideFrom i ∧ ¬ e ∈ invDarts X G₁.darts ∧
        ¬ e ∈ invDarts X G₂.darts) hlabW hn1 hn2 hnb' hna'
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
  refine ⟨faces, outerWalk, k, R₁, R₂, A₁, A₂, E, hCF, ?_, ?_, ?_⟩
  · rw [hk, hrot, hA₁, hA₂]
  · rcases hcase with ⟨hc₁, hc₂⟩ | ⟨hc, hc0⟩
    · refine Or.inl ⟨?_, ?_⟩
      · rcases hc₁ with hc₁ | hc₁
        · exact Or.inl fun r hr => (hc₁ r hr).1
        · exact Or.inr fun r hr => (hc₁ r hr).1
      · rcases hc₂ with hc₂ | hc₂
        · exact Or.inl fun r hr => (hc₂ r hr).1
        · exact Or.inr fun r hr => (hc₂ r hr).1
    · refine Or.inr ⟨fun r hr => ?_, ?_⟩
      · rcases hc r hr with hr' | hr'
        · exact Or.inl hr'.1
        · exact Or.inr hr'.1
      · rcases hc0 with h0 | h0
        · exact Or.inl (InputProof.length_eq_zero_of_invDarts_eq_nil A₁ (hA₁.symm.trans h0))
        · exact Or.inr (InputProof.length_eq_zero_of_invDarts_eq_nil A₂ (hA₂.symm.trans h0))
  · intro h0₁ h0₂
    apply hsub
    intro e he
    have hU₁nil : U₁ = [] := hA₁.trans (fourPieceInsideClose_invDarts_eq_nil A₁ h0₁)
    have hU₂nil : U₂ = [] := hA₂.trans (fourPieceInsideClose_invDarts_eq_nil A₂ h0₂)
    have hmem : e ∈ R₁ ++ U₁ ++ R₂ ++ U₂ := by
      rw [← hrot]
      exact List.mem_rotate.mpr he
    simp only [hU₁nil, hU₂nil, List.append_nil] at hmem
    rcases fourPieceInsideClose_mem_of_case hcase hmem with hpa | hpb
    · exact hpa.2
    · exact hpb.2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInsideClose_of_residual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
