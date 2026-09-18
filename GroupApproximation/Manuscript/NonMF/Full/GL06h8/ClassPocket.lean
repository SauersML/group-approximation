import GroupApproximation.Manuscript.NonMF.Full.GL06h7.Minimal
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h8: a nearest cell pocket somewhere in the class of a descent-minimal diagram

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).

## Planned proof

GL06h7's residual `GL06h7.gl06h7_minimalPocketStatement` asks for the nearest cell pocket
`GL06h4.gl06h4Nearest_Pocket` of every non-descending `Δ` itself.  Whether a diagram descends only
depends on `(rCellCount, |∂|)` (`GL06h7.gl06h7_descends_congr`).  So every least-area letter
diagram `Y` over the same `W` with `rCellCount Y = rCellCount Δ` and `|∂Y| = |∂Δ|` meets all of
GL06h7's hypotheses as well (`gl06h8_not_descends_of_class`).  Call these diagrams the class of
`Δ`.  GL06h5's strong induction only needs a pocket of one diagram in that class.  The residual
here, `gl06h8_classPocketStatement`, asks for exactly that.  This leaves the choice of the
diagram free, as in Osin's minimal choice.

* `gl06h8_classPocket_of_minimalPocket` (proved): GL06h7's residual gives this one, with
  `Y = Δ`.
* `gl06h8_descentPocket_of_classPocket` (proved): split on `GL06h6.gl06h6_Descends D ε Δ`.  A
  descent is the right disjunct of `GL06h5.gl06h5_descentPocketStatement`.  Otherwise the
  class member `Y` has the pocket, `rCellCount Y ≤ rCellCount Δ` and `|∂Y| = |∂Δ| ≤ ε + ε`.

## Strength

`GL06h7.gl06h7_minimalPocketStatement → gl06h8_classPocketStatement →`
`GL06h5.gl06h5_descentPocketStatement`, and no converse is known.
* It does not give GL06h7's residual.  The pocket it gives is a pocket of `Y`, and its `copy`
  is `O`-equivalent to `Y`, with the boundary word of `Y`.  `Y` shares only the cell count and
  the boundary length with `Δ`, not the boundary word, so it says nothing about the geometry of
  `Δ` itself.  GL06h7's residual asks for the pocket of every member of the class.  This one
  asks for the pocket of one member.
* GL06h5's statement does not give it.  At a non-descending `Δ`, GL06h5's left disjunct gives
  a pocket of some `Y`.  Its right disjunct would be a descent of `Δ`.  That `Y` has
  `rCellCount Y = rCellCount Δ`, since the pocket's nearest cell gives `0 < rCellCount Y`, and
  otherwise `Y` is a descent of `Δ`.  It has `|∂Δ| ≤ |∂Y| ≤ ε + ε`, with `|∂Y| > |∂Δ|`
  allowed.  This residual asks for `|∂Y| = |∂Δ|`.

## Truth check

It follows from GL06h7's residual (`gl06h8_classPocket_of_minimalPocket`), so it holds whenever
that one does.  GL06h7's truth check (one cell, the rose, two cells sharing an arc) goes through
unchanged with `Y = Δ`.  The nearest cell slit pocket (Osin's Lemma 9.7(b)) is expected to
exist at every non-descending `Δ`.  This statement asks for it at one diagram of the class only.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h8

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- **A nearest cell pocket in the class of a descent-minimal diagram** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  The residual of this lane: GL06h7's
pocket statement, asked of one least-area letter diagram with the same cell count and the same
boundary length as `Δ`, instead of `Δ` itself. -/
def gl06h8_classPocketStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W),
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        Delta.boundaryWord.length ≤ eps + eps → ¬ GL06h6.gl06h6_Descends D eps Delta →
          ∃ Y : DiscDiagram.{u, w, v} W, Y.LeastArea ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (Y.label d)) ∧
            Y.rCellCount = Delta.rCellCount ∧
            Y.boundaryWord.length = Delta.boundaryWord.length ∧
            Nonempty (GL06h4.gl06h4Nearest_Pocket D eps Y)

#audit_axioms GroupApproximation.Full.GL06h8.gl06h8_classPocketStatement

/-- **A class member does not descend either** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121).  A diagram with the cell count and the boundary length of a
non-descending `Δ` does not descend, so it meets all of GL06h7's hypotheses. -/
theorem gl06h8_not_descends_of_class {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (D : RelGenSet G Lambda) {eps : ℕ}
    {Delta Y : DiscDiagram.{u, w, v} W} (hc : Y.rCellCount = Delta.rCellCount)
    (hb : Y.boundaryWord.length = Delta.boundaryWord.length)
    (hno : ¬ GL06h6.gl06h6_Descends D eps Delta) : ¬ GL06h6.gl06h6_Descends D eps Y :=
  fun hY => hno (GL06h7.gl06h7_descends_congr D hc.symm hb.symm hY)

#audit_axioms GroupApproximation.Full.GL06h8.gl06h8_not_descends_of_class

/-- **GL06h7's residual gives this one** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): take `Y = Δ`. -/
theorem gl06h8_classPocket_of_minimalPocket
    (h : GL06h7.gl06h7_minimalPocketStatement.{u, w, v}) :
    gl06h8_classPocketStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta hlea hletters hW hcells hboundary hno
  exact ⟨Delta, hlea, hletters, rfl, rfl,
    h D eps W Delta hlea hletters hW hcells hboundary hno⟩

#audit_axioms GroupApproximation.Full.GL06h8.gl06h8_classPocket_of_minimalPocket

/-- **The descent from the class pocket** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): a descent is the right disjunct, and otherwise the class
member has the pocket. -/
theorem gl06h8_descentPocket_of_classPocket
    (h : gl06h8_classPocketStatement.{u, w, v}) :
    GL06h5.gl06h5_descentPocketStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta hlea hletters hW hcells hboundary
  by_cases hd : GL06h6.gl06h6_Descends D eps Delta
  · obtain ⟨Y, hleaY, hlettersY, hcountY, hshortY, hposY, hdesc⟩ := hd
    exact ⟨Y, hleaY, hlettersY, hcountY, hshortY, Or.inr ⟨hposY, hdesc⟩⟩
  · obtain ⟨Y, hleaY, hlettersY, hcountY, hlenY, hpocket⟩ :=
      h D eps W Delta hlea hletters hW hcells hboundary hd
    refine ⟨Y, hleaY, hlettersY, Nat.le_of_eq hcountY, ?_, Or.inl hpocket⟩
    rw [hlenY]
    exact hboundary

#audit_axioms GroupApproximation.Full.GL06h8.gl06h8_descentPocket_of_classPocket

/-- **The short-boundary refutation beyond thresholds, from the class pocket** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem gl06h8_shortBoundaryRefutedBelowSection_of_classPocket
    (h : gl06h8_classPocketStatement.{u, w, v}) :
    GL06h3.ShortBoundaryRefutedBelowSectionStatement.{u, w, v} :=
  GL06h5.gl06h5_shortBoundaryRefutedBelowSection_of_descent
    (gl06h8_descentPocket_of_classPocket h)

#audit_axioms
  GroupApproximation.Full.GL06h8.gl06h8_shortBoundaryRefutedBelowSection_of_classPocket

/-- **GL06e's all-cells clause, from the class pocket** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem gl06h8_allCellsShort_of_classPocket
    (h : gl06h8_classPocketStatement.{u, w, v}) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} :=
  GL06h5.gl06h5_allCellsShort_of_descent (gl06h8_descentPocket_of_classPocket h)

#audit_axioms GroupApproximation.Full.GL06h8.gl06h8_allCellsShort_of_classPocket

end GroupApproximation.Full.GL06h8
