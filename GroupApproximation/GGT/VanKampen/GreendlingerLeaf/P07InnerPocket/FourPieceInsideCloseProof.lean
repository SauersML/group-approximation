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
  have hd : A.darts = [] := List.eq_nil_of_length_eq_zero (by rw [CyclicArc.darts_length]; exact h)
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
