import GroupApproximation.Manuscript.NonMF.Full.GL06h6.Shortcut
import GroupApproximation.Manuscript.NonMF.Full.GL06h5.Descent
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h6: the descent up to the pocket of a shortcut-free diagram

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).

## Planned proof

Let `Δ` be as in `GL06h5.gl06h5_descentPocketStatement`.  Split on `gl06h6_Shortcut D ε Δ`.

* **A shortcut** (proved, `gl06h6_descends_of_shortcut`).  The pinch and fold-off lobes are
  enclosed shortcuts, and the non-geodesic simple sides are collar shortcuts.  Either one is a
  strict descent `Y`, the right disjunct.
* **No shortcut** (the residual `gl06h6_noShortcutPocketStatement`).  Every enclosed face set with
  a cell and outer walk at most `ε + ε` holds all cells and is at least as long as `∂Δ`.  Every
  following pocket with a cell whose side has a letter word of length at most `ε + ε` holds all
  cells, and that word is at least as long as `∂Δ`.  This is Osin's minimal choice of the
  subdiagram.  The residual asks for the nearest cell pocket `GL06h4.gl06h4Nearest_Pocket` of
  `Δ` itself, the left disjunct with `Y = Δ`.

The residual sits strictly between the two earlier statements:
`GL06h4.gl06h4Nearest_shortPocketStatement → gl06h6_noShortcutPocketStatement`
(`gl06h6_noShortcutPocket_of_shortPocket`, drop the extra hypothesis), and
`gl06h6_noShortcutPocketStatement → GL06h5.gl06h5_descentPocketStatement`
(`gl06h6_descentPocket_of_noShortcutPocket`, the split above).  No converse is known.  GL06h5's
statement does not produce a pocket of `Δ` itself.  GL06h4's statement asks for pockets of
diagrams with shortcuts too.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h6

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- **The nearest cell pocket of a shortcut-free diagram** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121).  The residual of this lane: GL06h4's pocket
statement under the extra hypothesis that `Δ` has no enclosed and no collar shortcut. -/
def gl06h6_noShortcutPocketStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W),
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        Delta.boundaryWord.length ≤ eps + eps → ¬ gl06h6_Shortcut D eps Delta →
          Nonempty (GL06h4.gl06h4Nearest_Pocket D eps Delta)

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_noShortcutPocketStatement

/-- **GL06h4's residual gives this one** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): forget the shortcut-free hypothesis. -/
theorem gl06h6_noShortcutPocket_of_shortPocket
    (h : GL06h4.gl06h4Nearest_shortPocketStatement.{u, w, v}) :
    gl06h6_noShortcutPocketStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta hlea hletters hW hcells hboundary _hno
  exact h D eps W Delta hlea hletters hW hcells hboundary

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_noShortcutPocket_of_shortPocket

/-- **The descent from the shortcut-free pocket** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): a shortcut descends, and otherwise `Y = Δ` has the pocket. -/
theorem gl06h6_descentPocket_of_noShortcutPocket
    (h : gl06h6_noShortcutPocketStatement.{u, w, v}) :
    GL06h5.gl06h5_descentPocketStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta hlea hletters hW hcells hboundary
  by_cases hs : gl06h6_Shortcut D eps Delta
  · obtain ⟨Y, hleaY, hlettersY, hcountY, hshortY, hposY, hdesc⟩ :=
      gl06h6_descends_of_shortcut D hlea hletters hs
    exact ⟨Y, hleaY, hlettersY, hcountY, hshortY, Or.inr ⟨hposY, hdesc⟩⟩
  · exact ⟨Delta, hlea, hletters, Nat.le_refl _, hboundary,
      Or.inl (h D eps W Delta hlea hletters hW hcells hboundary hs)⟩

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_descentPocket_of_noShortcutPocket

/-- **The short-boundary refutation beyond thresholds, from the shortcut-free pocket** (Osin,
proof of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem gl06h6_shortBoundaryRefutedBelowSection_of_noShortcutPocket
    (h : gl06h6_noShortcutPocketStatement.{u, w, v}) :
    GL06h3.ShortBoundaryRefutedBelowSectionStatement.{u, w, v} :=
  GL06h5.gl06h5_shortBoundaryRefutedBelowSection_of_descent
    (gl06h6_descentPocket_of_noShortcutPocket h)

#audit_axioms
  GroupApproximation.Full.GL06h6.gl06h6_shortBoundaryRefutedBelowSection_of_noShortcutPocket

/-- **GL06e's all-cells clause, from the shortcut-free pocket** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem gl06h6_allCellsShort_of_noShortcutPocket
    (h : gl06h6_noShortcutPocketStatement.{u, w, v}) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} :=
  GL06h5.gl06h5_allCellsShort_of_descent (gl06h6_descentPocket_of_noShortcutPocket h)

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_allCellsShort_of_noShortcutPocket

end GroupApproximation.Full.GL06h6
