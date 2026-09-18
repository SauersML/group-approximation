import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsFolParts
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-81: the pinched half and the top target are FALSE

**LOUD: verdict.**  `pinchAbsFol_PinchPart` (`PinchAbsFolParts.lean`) is FALSE, and so is
`PocketFourPieceOffStatement` (`AssemblyStatement.lean:77`).  Both fail on the GL03BPinch model
(`Manuscript/NonMF/Full/GL03BPinch/Statement.lean`).  This file proves no `¬ Statement`: that would
mean building the 48-dart diagram in Lean.  The certificate is a python check, re-derived from
the Lean definitions and independent of lane gl-p07-78's scripts:
`scratchpad/gl-p07-81/{model,walks,hyps,concl}.py`, run with `python3 concl.py`.  It reports
52 PASS out of 52.

## The model
* It has 48 darts, `V = 18`, `E = 24` and `F = 8`, with faces `Π_i`, `C`, `Π_j` (the hexagonal
  relator cells, in that order), the 12-gons `H₁` and `H₂`, the digons `a` and `b`, and the outer
  digon `o`.
* The group is trivial.  Every dart is labelled `base 1`, and `W = {[base 1]^6}`.
* `D.base = univ`, `eps = 1`, and the regions are `a = {a}` and `b = {b}`.  Both have
  `JoinsCells i j` and empty contact arcs.
* `K.walk = [s₁⁺] ++ invDarts ∂Π_i ++ [s₂⁺] ++ invDarts ∂Π_j`, and `G₁`, `G₂` are all of `∂Π_i`
  and `∂Π_j`.

## Hypotheses, each checked field by field
* **CombMap and planarity.**
  * `planar` holds: the map is connected and `χ = 18 - 24 + 8 = 2`.
  * Each face boundary is `nonempty`, `nodup`, `mem_iff`, `chain` and `closes`.
* **Cells.**
  * The relator cells are distinct and are not the outer face.
  * `relatorCell_word`, `inner_face` and `boundary_product` hold because the group is trivial.
  * `label_alpha` holds.
* **No side conditions.**  The hypotheses have no least-area, reducedness or `C'(λ)` condition.
  The only conditions on the words are that each has length `> 1` (here 6) and `IsLetter`, which
  holds because `D.base = univ`.
* **The regions `a` and `b`.**
  * `cycle_mem_iff` holds, and the `BoundaryStep` chain closes.
  * `boundary_decomposition` holds with empty arcs: `[s₂⁺, fa⁻] = [s₂⁺] ++ [fa⁻]`, and likewise
    for `b`.
  * Each side has length `≤ 1`.
  * `pasting` is a single shelling step.
  * `a` and `b` are disjoint.
* **The pocket walk.**
  * `hfirst`, `hsecond`, `hG₁` and `hG₂` hold, and so does every field of
    `IsNoncrossingClosedWalk`.
  * `sideFaces K.walk = {C, H₁, H₂, a, b}` and `hout` holds.
  * Both reclosed maps have `χ = 2`: the inner map has `(V, E, F) = (12, 14, 4)` and the outer
    map `(20, 24, 6)`.
  * `¬ FollowsBoundary` holds for `hw.outerCycle`, which fails at `s₁⁻` and `s₂⁻`.
* **The remaining premises.**
  * The cell `C` is in the side and in neither region.
  * `hcase` holds, since `a.cellArcList i = []`.
  * `hP` holds vacuously: there is no `EnclosedFaceSetSucc` walk on
    `witnessFaces = keepClass = {C, H₁, H₂}`.

## The conclusion fails
* **`pinchFollow_Conclusion`, first disjunct.**  No face set `S` with `C ∈ S ⊆ side` has a
  successor walk satisfying the dart clause.
* **`pinchFollow_Conclusion`, second disjunct.**  No successor walk lies on `∂Π_i` or on `∂Π_j`.
* **`pinchAbs_Cut`.**  `pinchAbs_set = {C, H₁, H₂}`, because `a` and `b` are bad.  Its complement
  has three boundary circuits: `∂Π_i`, `∂Π_j` and `[fa⁻, fb⁺]`.  All three touch `keepClass`, but
  each reversed side contains a face off `side K`: `Π_j`/`o`, `Π_i`/`o` and `Π_i`/`Π_j`
  respectively.  So `SUB` fails for all three.

## `PocketFourPieceOffStatement`, taking `C := C`
* The chunk clause forces every `R` entry into `{fa⁺, fb⁻}`.  So every walk dart lies in
  `{fa⁻, fb⁺} ∪ ∂Π_i ∪ ∂Π_j`.
* Under that bound, all 64 face sets containing `C` (and not `o`) were searched.  Bridge pairs
  were enumerated exactly.
* The search finds exactly one successor walk: `[fa⁻, fb⁺]` on `{C, H₁, H₂, Π_i, Π_j}`.
  * Its only decomposition has `A₁ = A₂ = []`, so the off-cell clause applies.
  * The off-cell clause asks for a cell off the set, and every cell is in the set.  So no witness
    exists.
* **Consequences.**
  * By `innerPocketEnclosed_of_fourPieceOff`, this matches the paper verdict of GL03BPinch that
    `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` is false.
  * By `pinchAbsFol_off_of_parts`, at least one of the two halves is false.  The pinched half is
    the one that fails here.

## The unconditional reductions proved below
* `pinchAbsPinchRefute_res_iff_out`: the fol residual is equivalent to the out residual.
* `pinchAbsPinchRefute_res_iff_parts`: the fol residual is equivalent to the conjunction of the
  two halves.
* `pinchAbsPinchRefute_notRes` and `pinchAbsPinchRefute_notOut`:
  a failure of the pinched half refutes both residuals.
* `pinchAbsPinchRefute_notParts`: a failure of the top target refutes one of the
  halves.
* `pinchAbsPinchRefute_notOff`: a failure of the target refutes the top target.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

/-- **LOUD: the two residuals are equivalent Props** (so both are false on the model). -/
theorem pinchAbsPinchRefute_res_iff_out :
    pinchAbsFol_ResidualStatement.{u, w, v} ↔ pinchAbsOut_ResidualStatement.{u, w, v} :=
  ⟨pinchAbsFol_out_of_statement, pinchAbsFol_of_out⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchRefute_res_iff_out

/-- **The split residual is exactly the conjunction of its two halves.** -/
theorem pinchAbsPinchRefute_res_iff_parts :
    pinchAbsFol_ResidualStatement.{u, w, v} ↔
      pinchAbsFol_FollowPart.{u, w, v} ∧ pinchAbsFol_PinchPart.{u, w, v} :=
  ⟨fun h => ⟨pinchAbsFol_followPart_of_res h, pinchAbsFol_pinchPart_of_res h⟩,
    fun h => pinchAbsFol_statement_of_parts h.1 h.2⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchRefute_res_iff_parts

/-- A counterexample to the pinched half refutes the split residual. -/
theorem pinchAbsPinchRefute_notRes (h : ¬ pinchAbsFol_PinchPart.{u, w, v}) :
    ¬ pinchAbsFol_ResidualStatement.{u, w, v} :=
  fun hr => h (pinchAbsFol_pinchPart_of_res hr)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchRefute_notRes

/-- A counterexample to the pinched half refutes the residual of gl-p07-74. -/
theorem pinchAbsPinchRefute_notOut (h : ¬ pinchAbsFol_PinchPart.{u, w, v}) :
    ¬ pinchAbsOut_ResidualStatement.{u, w, v} :=
  fun hr => h (pinchAbsFol_pinchPart_of_res (pinchAbsFol_of_out hr))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchRefute_notOut

/-- A counterexample to the top target refutes one of the two halves. -/
theorem pinchAbsPinchRefute_notParts (h : ¬ PocketFourPieceOffStatement.{u, w, v}) :
    ¬ (pinchAbsFol_FollowPart.{u, w, v} ∧ pinchAbsFol_PinchPart.{u, w, v}) :=
  fun hp => h (pinchAbsFol_off_of_parts hp.1 hp.2)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchRefute_notParts

/-- A counterexample to the P07 target refutes the top residual `PocketFourPieceOffStatement`. -/
theorem pinchAbsPinchRefute_notOff
    (h : ¬ P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v}) :
    ¬ PocketFourPieceOffStatement.{u, w, v} :=
  fun ho => h (innerPocketEnclosed_of_fourPieceOff ho)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchRefute_notOff

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
