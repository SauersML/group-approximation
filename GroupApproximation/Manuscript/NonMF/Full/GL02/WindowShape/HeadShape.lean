import GroupApproximation.Manuscript.NonMF.Full.GL02.WindowShape.HeadShapeDeps
import GroupApproximation.Manuscript.NonMF.Full.GL02.WindowShape.HeadShapeSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: the head shape of a class window arc (lane gl-p04-06)

*GL02 copy.*  Re-proof of the foreign module `Piece04.WindowShape.HeadShape`
(origin/main blob `5907a7057`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  `WindowHeadShapeStatement` is the
target of lane gl-p04-06: for a class `i` of kind `cell j`, a window `[x, y]` with `x` outside every
gap and nonempty run window, and an arc of `∂Π` with `arc.reverseDarts = classWindow k i x y`,
the run window and `arc.darts` have `RotationTurns.WindowHeadShape`.

## Truth check (T3 of the cartography, TRUE)

Write `σ`, `α`, `φ = σ α`.  By lane gl-p04-04 the class window is `γc ++ t :: rest` with
`runWindow = t :: T'`, and either `γc = []` or `γc = gap_s` starts with the class dart
`w = c_x`, where side `s` ends with `d = c_(x-1)` and the next class side `s'` starts with `t`.

* `arc.darts = (classWindow.map α).reverse = q' ++ α t :: γ` with `γ = (γc.map α).reverse`
  (`darts_eq_of_reverseDarts_eq`).
* If `γc = []`, `γ = []` and nothing is to be shown.
* Otherwise `γ.getLast = α w`.  Lane gl-p04-01 at `n = x - 1` gives `σ w = α d`.  Lane gl-p04-02
  gives `s < sideCount` and `s' = (s + 1) % sideCount`, and lane gl-p04-03 gives `φ d = t`.  So
  `σ (φ (α w)) = σ (σ w) = σ (α d) = φ d = t` (`headShape_of_split`).

The only degenerate case, an empty side, does not arise: lane gl-p04-04 already provides `t` and
the two side ends `d`, `t`.

## What is proved here

`windowHeadShape_of_deps`: the four upstream lane targets (stated in `HeadShapeDeps` as
`ClassStepStatement`, `ClassSidesSuccStatement`, `SideSuccFaceStatement`,
`WindowHeadSplitStatement`, since those lanes run in parallel) imply `WindowHeadShapeStatement`.
The assembly lane gl-p04-13 plugs in the four proofs.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.CaseOneWalk

/-- **The head shape of a class window arc** (lane gl-p04-06, `HeadShape.windowHeadShape`). -/
def WindowHeadShapeStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ) (j : Fin S.diagram.rCellCount) (x y : ℕ) (arc : CyclicArc (cellDarts S.diagram j)),
    i < Q.classCount k → Q.classKind k i = .cell j → x ≤ y → y ≤ (Q.word k i).length →
    ¬ Q.InGap k i x → Q.runWindow k i x y ≠ [] → arc.reverseDarts = Q.classWindow k i x y →
    RotationTurns.WindowHeadShape S.diagram.toCombMap (Q.runWindow k i x y) arc.darts

/-- **The head shape of a class window arc from lanes gl-p04-01 … 04.** -/
theorem windowHeadShape_of_deps (h01 : ClassStepStatement.{u, w, v})
    (h02 : ClassSidesSuccStatement.{u, w, v}) (h03 : SideSuccFaceStatement.{u, w, v})
    (h04 : WindowHeadSplitStatement.{u, w, v}) : WindowHeadShapeStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S P Q k i j x y arc hi hkind hxy hy hx hne harc
  obtain ⟨t, T', γc, rest, hT, hL, hγ⟩ := h04 Q k i x y hi hxy hy hx hne
  refine headShape_of_split (darts_eq_of_reverseDarts_eq arc harc) hL hT ?_
  rcases hγ with hγ | ⟨n, s, s', d, w, hx0, hd, hw, hγw, _, hs, hs', hdl, hth⟩
  · exact Or.inl hγ
  · refine Or.inr ⟨w, d, hγw, ?_, ?_⟩
    · have hx1 : x - 1 + 1 = x := by omega
      exact h01 Q k i j hi hkind (x - 1) d w hd (by rw [hx1]; exact hw)
    · obtain ⟨hlt, hsucc⟩ := h02 Q k i hi
      have hs'eq : s' = (s + 1) % P.sideCount k := hsucc n s s' hs hs'
      subst hs'eq
      exact h03 Q k s (hlt s (List.mem_of_getElem? hs)) d t hdl hth

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape.windowHeadShape_of_deps
