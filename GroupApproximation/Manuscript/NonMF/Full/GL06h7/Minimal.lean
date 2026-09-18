import GroupApproximation.Manuscript.NonMF.Full.GL06h6.Descent
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h7: the nearest cell pocket of a descent-minimal diagram

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).

## Planned proof

GL06h6's residual `GL06h6.gl06h6_noShortcutPocketStatement` asks for the nearest cell pocket
`GL06h4.gl06h4Nearest_Pocket` of every `Δ` with no enclosed and no collar shortcut.  GL06h5's
strong induction on `rCellCount · (ε + ε + 1) + |∂|` only ever needs the pocket at a `Δ` that
does not descend: its induction hypothesis refutes every strict descent `Y`.  The residual here,
`gl06h7_minimalPocketStatement`, asks for the pocket only under `¬ GL06h6.gl06h6_Descends`.

* `gl06h7_not_shortcut_of_not_descends` (proved): a shortcut descends
  (`GL06h6.gl06h6_descends_of_shortcut`), so a non-descending `Δ` has no shortcut.
* `gl06h7_minimalPocket_of_noShortcutPocket` (proved): GL06h6's residual gives this one.
* `gl06h7_descentPocket_of_minimalPocket` (proved): split on `gl06h6_Descends D ε Δ`.  A
  descent is the right disjunct of `GL06h5.gl06h5_descentPocketStatement`, and otherwise
  `Y = Δ` has the pocket.
* `gl06h7_descends_congr`, `gl06h7_descends_of_oEquivalent` (proved): whether `Δ` descends only
  depends on `(rCellCount Δ, |∂Δ|)`, so it transfers along an `O`-equivalence, for instance to
  the `copy` of a nearest pocket.

## Strength

The residual sits strictly between the two neighbouring statements:
`GL06h6.gl06h6_noShortcutPocketStatement → gl06h7_minimalPocketStatement → `
`GL06h5.gl06h5_descentPocketStatement`, and no converse is known.
* It does not give GL06h6's residual.  Let `W` have a relator `r` of length at most `ε + ε`
  whose one-cell diagram is least-area with letter labels.  Then every `Δ` with at least two
  cells descends (`gl06h7_descends_of_fewer`), so the residual says nothing over `W`.
  GL06h6's residual still asks for the pocket of every shortcut-free `Δ` there.  The descent
  `Y` is the unrelated one-cell diagram of `r`, and it says nothing about `Δ`'s geometry.
* GL06h5's statement does not give it.  At a non-descending `Δ`, GL06h5 gives a pocket of some
  `Y` with `rCellCount Y = rCellCount Δ` and `|∂Y| ≥ |∂Δ|`, not necessarily of `Δ` itself.

## Truth check

* One cell: excluded by `2 ≤ rCellCount Δ`.
* The rose (at least two cells glued at one vertex): each petal is an enclosed face set with
  one cell.  A petal of length at most `ε + ε` is an enclosed shortcut, so `Δ` descends.  If
  every petal is longer, then `|∂Δ| > ε + ε`.  Either way the residual is vacuous.
* Two cells sharing an arc: under `¬ Descends` it is GL06h4's nearest-pocket clause for this
  `Δ`, with the pocket the second cell seen from the first.  This clause holds whenever
  GL06h4's statement does.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h7

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- **The nearest cell pocket of a descent-minimal diagram** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121).  The residual of this lane: GL06h6's pocket
statement, asked only of a `Δ` that has no strict descent. -/
def gl06h7_minimalPocketStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W),
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        Delta.boundaryWord.length ≤ eps + eps → ¬ GL06h6.gl06h6_Descends D eps Delta →
          Nonempty (GL06h4.gl06h4Nearest_Pocket D eps Delta)

#audit_axioms GroupApproximation.Full.GL06h7.gl06h7_minimalPocketStatement

section Descends

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A non-descending diagram has no shortcut** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem gl06h7_not_shortcut_of_not_descends (D : RelGenSet G Lambda) {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} (hlea : Delta.LeastArea)
    (hletters : ∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d))
    (h : ¬ GL06h6.gl06h6_Descends D eps Delta) : ¬ GL06h6.gl06h6_Shortcut D eps Delta :=
  fun hs => h (GL06h6.gl06h6_descends_of_shortcut D hlea hletters hs)

#audit_axioms GroupApproximation.Full.GL06h7.gl06h7_not_shortcut_of_not_descends

/-- **Descending depends only on the cell count and the boundary length** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem gl06h7_descends_congr (D : RelGenSet G Lambda) {eps : ℕ}
    {Delta Delta' : DiscDiagram.{u, w, v} W} (hc : Delta'.rCellCount = Delta.rCellCount)
    (hb : Delta'.boundaryWord.length = Delta.boundaryWord.length)
    (h : GL06h6.gl06h6_Descends D eps Delta) : GL06h6.gl06h6_Descends D eps Delta' := by
  obtain ⟨Y, hleaY, hlettersY, hcountY, hshortY, hposY, hdesc⟩ := h
  refine ⟨Y, hleaY, hlettersY, ?_, hshortY, hposY, ?_⟩
  · rw [hc]
    exact hcountY
  · rw [hc, hb]
    exact hdesc

#audit_axioms GroupApproximation.Full.GL06h7.gl06h7_descends_congr

/-- **Descending transfers along an `O`-equivalence** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem gl06h7_descends_of_oEquivalent (D : RelGenSet G Lambda) {eps : ℕ}
    {Delta Delta' : DiscDiagram.{u, w, v} W} (E : OEquivalentDiscDiagram Delta Delta')
    (h : GL06h6.gl06h6_Descends D eps Delta) : GL06h6.gl06h6_Descends D eps Delta' :=
  gl06h7_descends_congr D E.rCellCount_eq (by rw [E.boundaryWord_eq]) h

#audit_axioms GroupApproximation.Full.GL06h7.gl06h7_descends_of_oEquivalent

/-- **A short least-area letter diagram with fewer cells is a descent** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  This is the witness that the
residual is vacuous over a `W` with a short one-cell least-area diagram. -/
theorem gl06h7_descends_of_fewer (D : RelGenSet G Lambda) {eps : ℕ}
    {Delta Y : DiscDiagram.{u, w, v} W} (hleaY : Y.LeastArea)
    (hlettersY : ∀ d, (symmetricLabelAlphabet D).IsLetter (Y.label d))
    (hshortY : Y.boundaryWord.length ≤ eps + eps) (hposY : 0 < Y.rCellCount)
    (hlt : Y.rCellCount < Delta.rCellCount) : GL06h6.gl06h6_Descends D eps Delta :=
  ⟨Y, hleaY, hlettersY, Nat.le_of_lt hlt, hshortY, hposY, Or.inl hlt⟩

#audit_axioms GroupApproximation.Full.GL06h7.gl06h7_descends_of_fewer

end Descends

/-- **GL06h6's residual gives this one** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): a non-descending `Δ` has no shortcut. -/
theorem gl06h7_minimalPocket_of_noShortcutPocket
    (h : GL06h6.gl06h6_noShortcutPocketStatement.{u, w, v}) :
    gl06h7_minimalPocketStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta hlea hletters hW hcells hboundary hno
  exact h D eps W Delta hlea hletters hW hcells hboundary
    (gl06h7_not_shortcut_of_not_descends D hlea hletters hno)

#audit_axioms GroupApproximation.Full.GL06h7.gl06h7_minimalPocket_of_noShortcutPocket

/-- **The descent from the minimal pocket** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): a descent is the right disjunct, and otherwise `Y = Δ` has the
pocket. -/
theorem gl06h7_descentPocket_of_minimalPocket
    (h : gl06h7_minimalPocketStatement.{u, w, v}) :
    GL06h5.gl06h5_descentPocketStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta hlea hletters hW hcells hboundary
  by_cases hd : GL06h6.gl06h6_Descends D eps Delta
  · obtain ⟨Y, hleaY, hlettersY, hcountY, hshortY, hposY, hdesc⟩ := hd
    exact ⟨Y, hleaY, hlettersY, hcountY, hshortY, Or.inr ⟨hposY, hdesc⟩⟩
  · exact ⟨Delta, hlea, hletters, Nat.le_refl _, hboundary,
      Or.inl (h D eps W Delta hlea hletters hW hcells hboundary hd)⟩

#audit_axioms GroupApproximation.Full.GL06h7.gl06h7_descentPocket_of_minimalPocket

/-- **The short-boundary refutation beyond thresholds, from the minimal pocket** (Osin, proof
of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem gl06h7_shortBoundaryRefutedBelowSection_of_minimalPocket
    (h : gl06h7_minimalPocketStatement.{u, w, v}) :
    GL06h3.ShortBoundaryRefutedBelowSectionStatement.{u, w, v} :=
  GL06h5.gl06h5_shortBoundaryRefutedBelowSection_of_descent
    (gl06h7_descentPocket_of_minimalPocket h)

#audit_axioms
  GroupApproximation.Full.GL06h7.gl06h7_shortBoundaryRefutedBelowSection_of_minimalPocket

/-- **GL06e's all-cells clause, from the minimal pocket** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem gl06h7_allCellsShort_of_minimalPocket
    (h : gl06h7_minimalPocketStatement.{u, w, v}) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} :=
  GL06h5.gl06h5_allCellsShort_of_descent (gl06h7_descentPocket_of_minimalPocket h)

#audit_axioms GroupApproximation.Full.GL06h7.gl06h7_allCellsShort_of_minimalPocket

end GroupApproximation.Full.GL06h7
