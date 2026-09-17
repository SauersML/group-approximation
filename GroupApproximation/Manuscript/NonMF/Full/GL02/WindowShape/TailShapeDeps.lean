import GroupApproximation.Manuscript.NonMF.Full.GL02.RotationTurns
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassSidesSucc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassStep
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.SideSuccFace
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: the tail shape, statements and list lemmas

*GL02 copy.*  Re-proof of the foreign module `Piece04.WindowShape.TailShapeDeps`
(origin/main blob `6f6b72c1a`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Lane `gl-p04-07`, step 4 of the
argument in `Piece04.RotationTurns`: "Let `u = U.last`, and write `p = γ (α u) p'`.  Either
`γ = []`, or the window ends at the start of side `s+1` and contains the whole gap `gap_s`, with
`u = side_s.last`.  Then `γ.head = α (gap_s.last) = σ side_(s+1).head = σ (φ u)`."

This module holds:

* `WindowTailShapeStatement`: the lane target (the text of `TailShapeStatement` in
  `WindowShape.Assembly`).
* `WindowTailSplitStatement`: the target of lane gl-p04-05, not on disk yet, stated with the
  exact lane text.  Lanes gl-p04-01, 02 and 03 are on disk (`WindowShape.ClassStep.sigma_succ`,
  `WindowShape.ClassSidesSucc.succ`, `WindowShape.SideSuccFace.facePerm_last`) and are used
  directly in `WindowShape.TailShape`.
* Three list lemmas: the arc of a class window, the head of a reversed mapped gap, and `1 ≤ y`
  when the class window ends with a nonempty gap.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.TailShape

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents

/-- **Tail shape of a class window arc** (lane gl-p04-07 target).  A run window of a cell-`j` class
that ends off a gap and is nonempty has the tail shape against the arc of its class window. -/
def WindowTailShapeStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ) (j : Fin S.diagram.rCellCount) (x y : ℕ) (arc : CyclicArc (cellDarts S.diagram j)),
    i < Q.classCount k → Q.classKind k i = .cell j → x ≤ y → y ≤ (Q.word k i).length →
    ¬ Q.InGap k i y → Q.runWindow k i x y ≠ [] → arc.reverseDarts = Q.classWindow k i x y →
    RotationTurns.WindowTailShape S.diagram.toCombMap (Q.runWindow k i x y) arc.darts

/-- **Tail split of a run window** (lane gl-p04-05 target, not yet on disk).  A nonempty run
window ending off a gap ends with `u`, and the class window is `rest ++ u :: γc` with `γc` empty or
the whole gap after the side of `u`. -/
def WindowTailSplitStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i x y : ℕ), i < Q.classCount k → x ≤ y → y ≤ (Q.word k i).length → ¬ Q.InGap k i y →
    Q.runWindow k i x y ≠ [] →
    ∃ (u : S.diagram.toCombMap.Dart) (U' γc rest : List S.diagram.toCombMap.Dart),
      Q.runWindow k i x y = U' ++ [u] ∧ Q.classWindow k i x y = rest ++ u :: γc ∧
      (γc = [] ∨ ∃ (n s s' : ℕ) (e g : S.diagram.toCombMap.Dart),
        (Q.classDarts k i)[y]? = some e ∧ (Q.classDarts k i)[y - 1]? = some g ∧
        γc.getLast? = some g ∧ γc = Q.gap k s ∧ (Q.classSides k i)[n]? = some s ∧
        (Q.classSides k i)[n + 1]? = some s' ∧ (P.sideDarts k s).getLast? = some u ∧
        (P.sideDarts k s').head? = some e)

/-- Mapping by `α` twice is the identity on lists. -/
theorem map_alpha_map_alpha {M : CombMap.{v}} (l : List M.Dart) :
    (l.map M.alpha).map M.alpha = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih, M.alpha_involutive a]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.TailShape.map_alpha_map_alpha

/-- An arc whose reversal is `rest ++ u :: γc` is `γ ++ α u :: p'` with `γ = (γc.map α).reverse`
and `p' = (rest.map α).reverse`. -/
theorem darts_eq_of_reverseDarts {M : CombMap.{v}} {cycle : List M.Dart} (arc : CyclicArc cycle)
    {rest γc : List M.Dart} {u : M.Dart} (h : arc.reverseDarts = rest ++ u :: γc) :
    arc.darts = (γc.map M.alpha).reverse ++ M.alpha u :: (rest.map M.alpha).reverse := by
  have hd : arc.darts = ((rest ++ u :: γc).map M.alpha).reverse := by
    rw [← h, CyclicArc.reverseDarts, map_alpha_map_alpha, List.reverse_reverse]
  rw [hd]
  simp only [List.map_append, List.map_cons, List.reverse_append, List.reverse_cons,
    List.append_assoc, List.singleton_append]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.TailShape.darts_eq_of_reverseDarts

/-- The head of `(γc.map α).reverse` is `α` of the last dart of `γc`. -/
theorem alpha_eq_of_head?_reverse_map {M : CombMap.{v}} {γc : List M.Dart} {g0 g : M.Dart}
    (hlast : γc.getLast? = some g0) (hg : (γc.map M.alpha).reverse.head? = some g) :
    M.alpha g0 = g := by
  rw [List.head?_reverse, List.getLast?_map, hlast] at hg
  simpa using hg

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.TailShape.alpha_eq_of_head?_reverse_map

section ClassWindow

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- A class window `[x, y]` that ends with a nonempty list after some dart has `1 ≤ y`. -/
theorem one_le_of_classWindow (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) {i x y : ℕ}
    {rest γc : List S.diagram.toCombMap.Dart} {u g : S.diagram.toCombMap.Dart}
    (hW : Q.classWindow k i x y = rest ++ u :: γc) (hlast : γc.getLast? = some g) : 1 ≤ y := by
  have hpos : 0 < γc.length := List.length_pos_iff.mpr (by rintro rfl; simp at hlast)
  have hlen : (rest ++ u :: γc).length ≤ y - x := by
    rw [← hW]
    exact List.length_take_le _ _
  simp only [List.length_append, List.length_cons] at hlen
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.TailShape.one_le_of_classWindow

end ClassWindow

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.TailShape
