import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RCellCase
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagramSuccAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04: the spanning relator-cell pairs from the class pocket enclosure

*GL02 copy.*  Re-proof of the foreign module `Piece04.RCellSpan`
(origin/main blob `8c12ebeca`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.4, Case 1, on class words.  This module reduces the
residual `ClassRCellSpanStatement` (module `Piece04.RCellCase`) to one smaller geometric statement,
`ClassPocketEnclosureStatement`, and derives from it `OsinLemma94ClassCaseOneRCellStatement`.

## Setting

`Γ = P.face k` is a polygon face, `Π = cell j` a relator cell, and `C` a backwards class pair whose
source and target classes are both of kind `cell j`.  Neither endpoint lies strictly inside a gap.  By
`cell_arc` each class, gaps included, is a reversed arc of `∂Π`, and the windows of `C` are the arcs
`p = sourceArc`, `q = targetArc`.  The face walk of `Γ` reads `X T Y S`, where `T` and `S` are the
side darts of the windows (`runWindow`, gaps removed).

## The isolated statement `ClassPocketEnclosureStatement` (OPEN)

There is a rotation `q B p A` of `∂Π`, and if `X B` and `Y A` are nonempty, one of the pockets
`B X` or `A Y` is the outside walk of an enclosed face set (successor form) that does not contain `Π`.

*Why it is true.*

1. *Gaps are loops at pinch vertices.*  Consecutive sides `s, s'` of one class are consecutive on the
   face walk of `Γ` (the run `T` or `S` is contiguous in `htrav`), and `s γ s'` is contiguous in the
   reversed arc of `∂Π`.  So the gap `γ` is a closed walk along `∂Π` at the end vertex `z` of `s`.
   If `γ ≠ []`, `z` is a pinch of `∂Π`.  Around `z` the corners read `s, [Π], γ, [Π], s', [Γ]`, so the
   component `R_γ` of `S² ∖ cl Π` bounded by `γ` does not contain `Γ`.  Every edge of `γ` has `Π` on
   one side and `R_γ` or `Π` on the other.  So no dart of `Γ` is a gap dart.
2. *The windows are disjoint arcs.*  Each window contains a side dart: a window without one runs
   from the start to the end of one gap, so its endpoint vertices agree (`gap_value`), against
   `source_long`, `target_long` (`ε < d(·,·)`).  A side dart of one class is a dart of `Γ`.  It is not
   a side dart of the other class (`classSides_disjoint`, the face walk has no repeated dart) and not
   a gap dart (step 1).  Two cyclic arcs of `∂Π` that overlap without either one containing a side dart
   of the other would have to meet inside gaps only.  But a gap is flanked by sides of its class
   (`gap_last`), and so the overlap reaches a side.  So `p` and `q` are disjoint and nonempty, and
   `∂Π` rotates to `q B p A`.
3. *Pockets.*  `B X` and `A Y` are closed walks: `B` runs from the start vertex `b'` of the target
   window to the end vertex `a'` of the source window, and `X` runs from `a'` to `b'` (`hX`).
   Likewise for `A Y`.  A Jordan curve through the interiors of `Γ` and `Π`, crossing one side edge
   of `p` and one of `q`, separates the pocket between `X` and `B` from the pocket between `Y` and
   `A`.  So the outer face lies in at most one of them.  Take `F` to be the faces of the other pocket
   together with the pinch-loop regions of `B` (or `A`) on its side, and without the regions `R_γ` of
   the gap loops.  These lie off the pocket by step 1.  The walk has only faces `Γ`, `Π` on its left.
   It is duplicate-free, it is exactly the set of darts leaving `F`, and it turns to its successor.
   The last point is the side-level spur enclosure `osinLemma94CaseOneSpurEnclosure` and the
   noncrossing enclosure, applied to the same pocket.  The gap loops attach to `∂Π` between two
   `Π`-corners, so they are not met by the turns of `B X`.

## The reduction proved here

Let `C` be a residual pair.  Take the rotation `q B p A` of the isolated statement.  The hypothesis
`hval` of the residual gives `X B ≠ 1` and `Y A ≠ 1`, so both are nonempty and one pocket is enclosed,
say `B X` with face set `F`.

* `F` holds a relator cell.  Otherwise the enclosed subdiagram `closedWalkEnclosedSubdiagramSucc` has
  none, and `(B X)⁻¹` reads `1`, against `X B ≠ 1`
  (`SameCellSpurEnclosure.listVal_eq_one_of_enclosedSucc`).
* `B` is an arc of `∂Π`, from the rotation `q B p A` (`CyclicArc.exists_darts_eq_of_rotate_eq`), and
  `(B X)⁻¹ = X⁻¹ B⁻¹`.  The word `X⁻¹` has norm at most `ε`: `X` joins the end vertices of the pair,
  so its value is that of the end connector (`wordNorm_lt_of_end_connector`).
* The restricted loop cut `enclosedSubdiagramLoopCutSuccLong` (relator words are longer than one
  letter since `ρ ≥ 2`) gives a loop cut.  `OsinLoopCut.false_of_below` kills it by least area and
  the induction hypothesis `hbelow`, at `ρ ≥ ρ₁` of `SameCellSimplePocket.exists_rho_large`.
* `A Y` is symmetric, with the start connector.

These are the steps of the side-level spur branch `osinLemma94CaseOneRCellSpur_of_enclosureLong`,
with the side arcs replaced by the class windows.

## Contents

* `ClassPocketEnclosureStatement` (OPEN): the rotation and the pocket enclosure on class windows.
* `false_of_enclosedPocket`: an enclosed pocket with a short connector part and value `≠ 1` is
  refuted.
* `rCellSpan_of_classPocketEnclosure`, `rCell_of_classPocketEnclosure`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.CaseOneWalk

/-- **The class pocket enclosure** (OPEN).  For a backwards class pair of one relator cell `Π`, with
no endpoint inside a gap, the windows are disjoint arcs of `∂Π`, so that `∂Π` rotates to `q B p A`.
If `X B` and `Y A` are nonempty, one of the pockets `B X`, `A Y` encloses a face set without `Π`. -/
def ClassPocketEnclosureStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps),
    C.b' < C.b → ¬ Q.GapEndpoint k C →
    ∀ (j : Fin S.diagram.rCellCount) (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
      (X Y : List S.diagram.toCombMap.Dart) (r : ℕ),
      Q.classKind k C.source = .cell j → Q.classKind k C.target = .cell j →
      (S.diagram.faceBoundary (P.face k)).darts.rotate r =
        X ++ Q.runWindow k C.target C.b' C.b ++ Y ++ Q.runWindow k C.source C.a C.a' →
      sourceArc.reverseDarts = Q.classWindow k C.source C.a C.a' →
      targetArc.reverseDarts = Q.classWindow k C.target C.b' C.b →
      ∃ (n : ℕ) (B A : List S.diagram.toCombMap.Dart),
        (cellDarts S.diagram j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A ∧
        (X ++ B ≠ [] → Y ++ A ≠ [] →
          (∃ F : Finset S.diagram.toCombMap.Face,
              EnclosedFaceSetSucc S.diagram F (B ++ X) ∧ (cell S.diagram j).face ∉ F) ∨
            ∃ F : Finset S.diagram.toCombMap.Face,
              EnclosedFaceSetSucc S.diagram F (A ++ Y) ∧ (cell S.diagram j).face ∉ F)

open SameCellRCellEnclosed SameCellSpurEnclosure in
/-- **An enclosed pocket is refuted.**  A pocket `B Z` enclosing a face set without `Π`, with `B` an
arc of `∂Π`, `Z⁻¹` of norm at most `ε` and `Z B ≠ 1`, gives a loop cut, which least area and the
induction hypothesis kill. -/
theorem false_of_enclosedPocket {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu)
    (hmu1 : mu ≤ 1 / 16) {eps rho : ℕ}
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ)) (hrho : 2 ≤ rho)
    {W : Set (List (RelLetter G Lambda))} (hW : OsinCCondition D W eps mu lambda c rho)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (hleast : Delta.LeastArea)
    (hbelow : ∀ (Xi : DiscDiagram.{u, w, v} W) (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
      Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
        ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi, OsinLemma97bConclusion mu T)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {j : Fin S.diagram.rCellCount} {F : Finset S.diagram.toCombMap.Face}
    {Z B : List S.diagram.toCombMap.Dart}
    (hF : EnclosedFaceSetSucc S.diagram F (B ++ Z)) (hcellOut : (cell S.diagram j).face ∉ F)
    (hB : ∃ arc : CyclicArc (cellDarts S.diagram j), arc.darts = B)
    (hnorm : WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord S.diagram (invDarts S.diagram Z))) ≤ eps)
    (hval : RelLetter.listVal (dartWord S.diagram (Z ++ B)) ≠ 1) : False := by
  have hrho0 : 0 < rho := by omega
  have hlong := one_lt_length_of_two_le_rho hW hrho
  obtain ⟨C₀, hC₀, hCf⟩ : ∃ C ∈ S.diagram.relatorCells, C.face ∈ F := by
    by_contra hno
    exact listVal_invDarts_append_ne_one hval
      (listVal_eq_one_of_enclosedSucc closedWalkEnclosedSubdiagramSucc hF
        fun C hC hmem => hno ⟨C, hC, hmem⟩)
  obtain ⟨Barc, hBarc⟩ := hB
  have hdecomposition : invDarts S.diagram (B ++ Z) =
      invDarts S.diagram Z ++ invDarts S.diagram Barc.darts := by
    rw [hBarc]
    simp only [invDarts, List.reverse_append, List.map_append]
  obtain ⟨cut⟩ := enclosedSubdiagramLoopCutSuccLong D eps rho mu lambda c hW hlambda1 hc hlong
    Delta S.diagram hleast S.equiv S.label_admissible F (B ++ Z) hF C₀ hC₀ hCf j hcellOut Barc
    (invDarts S.diagram Z) hdecomposition hnorm
  exact cut.false_of_below o52LeastArea hW hlambda hmu hmu1 hrho0 hlarge hleast
    (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt)

/-- **The spanning relator-cell pairs from the class pocket enclosure.**  The enclosed pocket
`B X` or `A Y` is refuted by `false_of_enclosedPocket`, with the end or the start connector. -/
theorem rCellSpan_of_classPocketEnclosure (hencl : ClassPocketEnclosureStatement.{u, w, v}) :
    ClassRCellSpanStatement.{u, w, v} := by
  intro G _ Lambda D _hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max 2 rho1, by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast _hpos hbelow S _hcard _hmin P _hmax Q k C hback hnogap _hnotsingle
    _hsv j sourceArc targetArc X Y r hks hkt htrav hsource htarget hX hY hval
  have hlarge := hrho1 rho (le_of_max_le_right hrho)
  have hrho2 : 2 ≤ rho := le_of_max_le_left hrho
  obtain ⟨n, B, A, hPi, hcases⟩ :=
    hencl Q k C hback hnogap j sourceArc targetArc X Y r hks hkt htrav hsource htarget
  obtain ⟨hXB, hYA⟩ := hval n B A hPi
  rcases hcases (SameCellRCellAssembly.append_ne_nil_of_listVal_ne_one hXB)
      (SameCellRCellAssembly.append_ne_nil_of_listVal_ne_one hYA) with
    ⟨F, hF, hcellOut⟩ | ⟨F, hF, hcellOut⟩
  · have hrot : (cellDarts S.diagram j).rotate (n + targetArc.darts.length) =
        B ++ (sourceArc.darts ++ A ++ targetArc.darts) := by
      rw [← List.rotate_rotate, hPi]
      simp only [List.append_assoc]
      rw [List.rotate_append_length_eq]
      simp only [List.append_assoc]
    have hnorm : WordMetric.wordNorm D.alphabet.carrier
        (RelLetter.listVal (dartWord S.diagram (invDarts S.diagram X))) ≤ eps := by
      rw [listVal_dartWord_invDarts, WordMetric.wordNorm_inv D.alphabet.symmetricGenerating]
      exact (wordNorm_lt_of_end_connector C hX).le
    exact false_of_enclosedPocket hlambda hlambda1 hc hmu hmu1 hlarge hrho2 hW hleast hbelow S hF
      hcellOut (CyclicArc.exists_darts_eq_of_rotate_eq hrot) hnorm hXB
  · have hrot : (cellDarts S.diagram j).rotate
        (n + (targetArc.darts ++ B ++ sourceArc.darts).length) =
          A ++ (targetArc.darts ++ B ++ sourceArc.darts) := by
      rw [← List.rotate_rotate, hPi, List.rotate_append_length_eq]
    have hnorm : WordMetric.wordNorm D.alphabet.carrier
        (RelLetter.listVal (dartWord S.diagram (invDarts S.diagram Y))) ≤ eps := by
      rw [listVal_dartWord_invDarts, WordMetric.wordNorm_inv D.alphabet.symmetricGenerating]
      exact (wordNorm_lt_of_start_connector C hY).le
    exact false_of_enclosedPocket hlambda hlambda1 hc hmu hmu1 hlarge hrho2 hW hleast hbelow S hF
      hcellOut (CyclicArc.exists_darts_eq_of_rotate_eq hrot) hnorm hYA

/-- **The relator-cell branch of GapSpan from the class pocket enclosure.** -/
theorem rCell_of_classPocketEnclosure (hencl : ClassPocketEnclosureStatement.{u, w, v}) :
    OsinLemma94ClassCaseOneRCellStatement.{u, w, v} :=
  rCell_of_span (rCellSpan_of_classPocketEnclosure hencl)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.false_of_enclosedPocket
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.rCellSpan_of_classPocketEnclosure
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.rCell_of_classPocketEnclosure
