import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.ExitOrder
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.EnclosedRotate
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunSplit
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, case (d): the order of the walk from one face block

Lane `gl-p06-02`.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed
sentence on its own.

## What this module proves

* `cellOff_of_block`: a nonempty block of walk darts on the face of `Π_k` puts `Π_k`
  off the enclosed face set.
* `exists_arc_of_block`: suppose a rotation of the outside walk of an `EnclosedFaceSetSucc`
  reads `u ++ v`, the darts of `u` lie on the face of `Π_k`, and each step of `u` is a kept face
  successor or has no pinch.  Then `u ++ v` is again an enclosed successor walk, and its reverse
  reads `v̄ ++ Ā` for an arc `A` of `Π_k` with `A.darts = u`.
* `caseDOrder_of_block`: `P06LakeCell.CaseDLakeRelatorOrderStatement` from
  `CaseDBlockStatement`.

## The remaining statement

`CaseDBlockStatement` (OPEN) keeps every hypothesis of
`P06LakeCell.CaseDLakeRelatorOrderStatement`.  Its one-arc disjunct asks for an enclosed
successor face set holding a relator cell, and a cell `Π_k`, with:

* a rotation `ow.rotate s = u ++ v` of the outside walk;
* every dart of `u` on the face of `Π_k`;
* each step of `u` either a kept face successor of `u ++ v` or free of a pinch;
* `(cell X k).face ∉ faces ∨ u ≠ []`;
* every dart of `v` on `K.firstSide ++ K.secondSide`.

Its other disjunct (the two-arc exit) is unchanged.

**Why it is weaker.**  The target implies it literally.  Take `s = 0`, `u = A.darts` and
`v = invDarts P`.  Then `outerWalk = A.darts ++ invDarts P` by the involution
`Embedded.invDarts_invDarts`.  Arc darts are consecutive under `facePerm`, so each step is kept.
The darts of `v` are the reverses of `P`, and these lie on the sides.  The converse is not free.
The residual lets the walk start anywhere.  It gives the `Π_k` contact only as a list of darts
on that face with local step conditions, not as an arc.  It lets `u ≠ []` stand in for
`Π_k ∉ faces`.  The reduction supplies these facts:

* the rotation (`P07InnerPocket.EnclosedFaceSetSucc.rotate`);
* the chain `facePerm u[t] = u[t+1]` (`P07InnerPocket.PocketRun.succ_eq_facePerm`);
* duplicate freeness (`run_nodup`);
* the arc (`exists_cyclicArc_of_isChain`);
* the reverse (`Embedded.invDarts_append`);
* the off-face fact (`EnclosedFaceSet.mem_iff`).

**Truth check.**  The only small models in the tree are the `GL03BPinch` 48-dart model
(`gl-p07-81`, scratch `model.py`), with the trivial group, `ε = 1`, `rCellCount = 3`.  They do
not meet the hypotheses.

* `X.LeastArea` fails.  In the trivial group every boundary value is `1`, the empty product, so
  `LeastArea` forces `rCellCount = 0`.  But `i ≠ j` needs two cells.
* The second-cell hypothesis `hsec` fails.  There `lakeOf K i = {Π_i}`.
* The strict first-arc hypothesis fails.

So the models neither refute nor test the target, and no refutation is possible there.  The
paper route of `P06LakeCell.ExitOrder` supports the residual.  Let `H` be the piece of the second
relator cell in the complement of `K.faces ∪ {Π_i}`, with its lakes filled.

* If `Π_j ∉ H`, the reverse outside walk of `H` meets `Π_i` in one arc and otherwise lies on the
  sides.  Rotated to start at that arc, this is the block form with `k = i`.
* If `Π_j ∈ H`, the second disjunct applies.

What stays open is building `H` and the order of its walk.  Both are paper-level only.

## Manuscript status

Infrastructure for `thm:hull`; certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeOrder

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

section Block

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- **A nonempty face block is off the face set**: a nonempty prefix of an enclosed walk whose
darts lie on the face of `Π_k` shows `Π_k ∉ faces`. -/
theorem cellOff_of_block {faces : Finset X.toCombMap.Face}
    {u v : List X.toCombMap.Dart} (k : Fin X.rCellCount)
    (E : EnclosedFaceSetSucc X faces (u ++ v))
    (hu : ∀ x ∈ u, X.toCombMap.faceOf x = (cell X k).face)
    (hoff : (cell X k).face ∉ faces ∨ u ≠ []) : (cell X k).face ∉ faces := by
  rcases hoff with hoff | hne
  · exact hoff
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil u hne
    have hmem := (E.mem_iff x).mp (List.mem_append_left v hx)
    rw [← hu x hx]
    exact hmem.1

/-- **A face block of a rotated walk is an arc read backwards.**  If a rotation of an enclosed
successor walk reads `u ++ v`, with `u` on the face of `Π_k` and every step of `u` kept or
pinch free, then `u ++ v` is an enclosed successor walk whose reverse is `v̄ ++ Ā`, for an arc
`A` of `Π_k`. -/
theorem exists_arc_of_block {faces : Finset X.toCombMap.Face}
    {ow u v : List X.toCombMap.Dart} {s : ℕ} (k : Fin X.rCellCount)
    (E : EnclosedFaceSetSucc X faces ow) (hs : ow.rotate s = u ++ v)
    (hu : ∀ x ∈ u, X.toCombMap.faceOf x = (cell X k).face)
    (hstep : ∀ (t : ℕ) (ht : t + 1 < u.length),
      walkKeep X.toCombMap (u ++ v) (X.toCombMap.facePerm u[t]) ∨
        P07InnerPocket.PocketRun.PinchFreeAt X.toCombMap u[t]) :
    ∃ A : CyclicArc (cellDarts X k), EnclosedFaceSetSucc X faces (u ++ v) ∧
      invDarts X (u ++ v) = invDarts X v ++ invDarts X A.darts := by
  have E' : EnclosedFaceSetSucc X faces (u ++ v) := by
    rw [← hs]
    exact P07InnerPocket.EnclosedFaceSetSucc.rotate E s
  have hchain : ∀ (t : ℕ) (ht : t + 1 < u.length),
      X.toCombMap.facePerm u[t] = u[t + 1] := by
    intro t ht
    have hlt : t + 1 < (u ++ v).length := by rw [List.length_append]; omega
    have hg0 : (u ++ v)[t]'(by omega) = u[t]'(by omega) := List.getElem_append_left (by omega)
    have hg1 : (u ++ v)[t + 1]'hlt = u[t + 1] := List.getElem_append_left ht
    have hmain := P07InnerPocket.PocketRun.succ_eq_facePerm E' t hlt (by
      rw [hg0, hg1]
      rcases hstep t ht with hkeep | hpinch
      · exact Or.inl hkeep
      · exact Or.inr ⟨hpinch, (hu _ (List.getElem_mem ht)).trans
          (hu _ (List.getElem_mem (by omega))).symm⟩)
    rw [hg0, hg1] at hmain
    exact hmain
  obtain ⟨A, hA⟩ : ∃ A : CyclicArc (cellDarts X k), A.darts = u :=
    P07InnerPocket.PocketRun.exists_cyclicArc_of_isChain (X.faceBoundary (cell X k).face) u
      (P07InnerPocket.PocketRun.run_nodup (u := u) (v := v) E' rfl)
      (fun x hx => ((X.faceBoundary (cell X k).face).mem_iff x).mpr (hu x hx))
      (List.isChain_iff_getElem.mpr hchain)
  exact ⟨A, E', by rw [Embedded.invDarts_append, hA]⟩

end Block

/-- **Case (d), one face block of the walk of the filled piece** (OPEN).  Every hypothesis of
`P06LakeCell.CaseDLakeRelatorOrderStatement`.  It concludes an enclosed successor face set
holding a relator cell, one of whose outside walk rotations reads a block on the face of a cell
`Π_k` (with kept or pinch free steps) and then side darts of `K`, or the two-arc exit. -/
def CaseDBlockStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∀ (eps rho : ℕ) (W : Set (List (RelLetter G Lambda))),
        OsinCCondition D W eps mu lambda c rho →
          ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j → X.LeastArea →
            OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount →
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
            ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
              K.firstArc.length < (cellDarts X i).length →
              K.secondArc.length < (cellDarts X j).length →
              ¬Unpinched X.toCombMap K.faces → Piece06.AllNonFirstTurnsCrossed K →
              ¬ Piece06.CellCut K → (∀ k : Fin X.rCellCount, ¬ Piece06.SideCell K k) →
              Piece06.ShortPetalFree eps X → ¬ Piece06.CellFilterMove K →
              P06LakeCell.Assembly.AllCellsEnclosed K →
              (∃ C ∈ X.relatorCells,
                C.face ∈ P06LakeCell.lakeOf K i ∧ C.face ≠ (cell X i).face) →
                (∃ (faces : Finset X.toCombMap.Face) (ow u v : List X.toCombMap.Dart) (s : ℕ)
                  (k : Fin X.rCellCount),
                  EnclosedFaceSetSucc X faces ow ∧
                    (∃ C ∈ X.relatorCells, C.face ∈ faces) ∧
                    ((cell X k).face ∉ faces ∨ u ≠ []) ∧ ow.rotate s = u ++ v ∧
                    (∀ x ∈ u, X.toCombMap.faceOf x = (cell X k).face) ∧
                    (∀ (t : ℕ) (ht : t + 1 < u.length),
                      walkKeep X.toCombMap (u ++ v) (X.toCombMap.facePerm u[t]) ∨
                        P07InnerPocket.PocketRun.PinchFreeAt X.toCombMap u[t]) ∧
                    ∀ x ∈ v, x ∈ K.firstSide ++ K.secondSide) ∨
                  Piece06.LakeFillTwoArcExit D eps X

/-- **Case (d) order of the walk from one face block**: rotate, turn the block into an arc,
and read the side darts backwards. -/
theorem caseDOrder_of_block (h : CaseDBlockStatement.{u, w, v}) :
    P06LakeCell.CaseDLakeRelatorOrderStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16 eps rho W hcondition X i j hij
    hlea hbelow hlabel K hK hnft hfirst hsecond hpinch hrose hcut hsideCell hshort hmove hall hsec
  rcases h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16 eps rho W hcondition X i j hij hlea
      hbelow hlabel K hK hnft hfirst hsecond hpinch hrose hcut hsideCell hshort hmove hall
      hsec with ⟨faces, ow, u, v, s, k, E, hC, hoff, hs, hu, hstep, hv⟩ | htwo
  · obtain ⟨A, E', hdec⟩ := exists_arc_of_block k E hs hu hstep
    refine Or.inl ⟨faces, u ++ v, invDarts X v, k, A, E', hC,
      cellOff_of_block k E' hu hoff, hdec, ?_⟩
    intro e he
    exact hv _ ((Embedded.mem_invDarts_iff v e).mp he)
  · exact Or.inr htwo

/-- **Case (d) exit from one face block**: `P06LakeCell.CaseDLakeRelatorExitStatement` from
`CaseDBlockStatement`. -/
theorem caseDExit_of_block (h : CaseDBlockStatement.{u, w, v}) :
    P06LakeCell.CaseDLakeRelatorExitStatement.{u, w, v} :=
  P06LakeCell.caseDLakeRelatorExit_of_order (caseDOrder_of_block h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeOrder

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeOrder.cellOff_of_block
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeOrder.exists_arc_of_block
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeOrder.CaseDBlockStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeOrder.caseDOrder_of_block
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeOrder.caseDExit_of_block
