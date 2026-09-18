import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchRestDoneStep
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchRestDoneStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCaseProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDoneRead
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDoneOff
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-68: clause (rest) from the pinched residual

The target is `PinchCase.RestStatement`.  Write `F = witnessFaces a b K C.face`.  A witness walk
is `ow` with `EnclosedFaceSetSucc X F ow` and `faceOf (α d) ∈ F` on `ow`.  Also write (N) for the
four noninterleave clauses, (S) for the four step clauses S1a, S1b, S2a, S2b, and (nd) for "all
four contact arcs nonempty".  A walk is *good* when (N) and (S) hold.

## The math: the case split of (rest)

Case (i) fails, so one of these holds.
1. **A good witness walk exists.**  Branch 1 holds with `faces = F`
   (`PinchCase.rest_of_residual`, lane gl-p07-34).  Clause 1 comes from `mem_witnessFaces_self`
   and `witnessFaces_subset_sideFaces`, clause 2' from `dart_clause`, clause 3 from (N), and clauses
   4a/4b from (S) via `ArcClose.arc_of_block` / `arc_of_all`.  **Closed.**
2. **(nd) and a witness walk `ow` satisfying (S).**  (N) holds for *every* witness walk once (nd)
   holds.  This is the now-proved nondegenerate machinery, `witnessStepDone_noninterleave`
   (lane gl-p07-67), and it needs no pinch-freeness.  So `ow` is good, and case 1 applies.
   **Closed.**
3. **(nd) or (N), with a witness walk `ow` whose `G`-darts are all pinch-free.**  Then (S) holds
   for `ow` (`pinchRestDone_stepGood`, `PinchRestDoneStep.lean`): every step clause is about
   positions where `ow[p]` is pinched.  With (N), from (nd) by case 2 or given directly, `ow` is
   good.  **Closed.**  Case (i) fails here, so this is exactly the configuration where `Π_i` or
   `Π_j` has pinches, but none on the walk.  It occurred 72 times in the models below.
4. **Otherwise** there is no witness walk, or every witness walk with (nd) or (N) fails (S) at a
   pinched dart of `G₁ ∪ G₂`, or the walk has a degenerate arc and fails (N).  This is the residual
   `pinchRestDone_ResidualStatement` (`PinchRestDoneStatement.lean`).  Its extra hypothesis (P) is
   derived in `pinchRestDone_pinchCaseResidual` from "no good walk" via cases 2 and 3.

## LOUD: strength of the residual

* **Equivalent as a Prop.**  `pinchRestDone_rest_of_residual` and `pinchRestDone_residual_of_rest`
  are both proved.  So is the step to lane 34's LOUD-equivalent `PinchCase.ResidualStatement`
  (`pinchRestDone_pinchCaseResidual`).  No residual cut out of `RestStatement` by hypotheses can
  be strictly weaker as a Prop.
* **Strictly smaller in proof content**, even compared with `PinchCase.ResidualStatement`.  That
  statement's hypothesis "no good walk" does not give (P) by definition alone: that takes the
  nondegenerate noninterleave theorem `witnessStepDone_noninterleave` (a large proof, lanes
  gl-p07-32 to 67) and the pinch lemma.  So a prover of the new residual may assume that
  - with (nd), every witness walk fails (S), and
  - every such failure sits on a pinched dart.
  Prior residuals had to exclude the (nd)-and-(N)-fails branch and the pinch-free-walk branch by
  hand.
* **Not false** (its truth is inherited from `RestStatement`, open and plausible).  It is not
  one of the AVOIDed FALSE statements, and it routes through none of them.

## Truth check (python, `scratchpad/gl-p07-68/rest_check.py`, gl-p07-64/65 grid maps)

The random runs (seeds 11, 12, 13 and 21 with 300 maps at 9 mutations; seeds 31, 32 and 33 with
400 maps at 25 mutations) gave 3 471 configurations, all in case (i).  The biased lobe search
(`pinch_run.py`, 11 seeds) found 90 more rest configurations.  Exhaustive lobes in columns 1–2
(`pinch_enum.py`, 6×6 and 7×5 grids, 4 `J` tweaks) gave 125 630 configurations; 15 540 fall
under (rest).  All 15 540 have a good witness walk, so all are closed by cases 1 to 3.  Of these,
72 are case 3 with no pinch on the walk.  **Zero** configurations reach the residual, so the
residual is vacuous on every model.  The counters `BAD_nondeg_N_fails` (checking case 2) and
`BAD_pfwalk_S_fails` (checking case 3) stayed at 0.

**LOUD: the grid models never produce degenerate (empty) contact arcs**, because
`decompositions` only returns nonempty arcs.  So the degenerate half of the residual is untested
by python; the paper models T2, M2, M8, M9 and M11 of lanes 21 to 34 cover it (see
`PinchCaseResidualStatement.lean`).

## Riskiest point

As in lanes 31, 34 and 37c: pinch pathologies where every witness walk steps across a pinched
dart without keeping `facePerm` (model M11: branch 2 needed), or degenerate-arc interleaving
(model M9: branch 1 with `faces = sideFaces K.walk`).  Both need a *new* face set with its own
`EnclosedFaceSetSucc` walk.  The corpus's only general constructor,
`enclosedFaceSetSuccOfNoncrossing`, needs a `FollowsBoundary` hypothesis that the premise block
does not supply.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Lane 34's residual from the pinched residual.**  "No good walk" gives (P): with (nd), (N)
comes from `witnessStepDone_noninterleave`; then (S) fails, and `pinchRestDone_exists_pinched`
gives the pinched dart. -/
theorem pinchRestDone_pinchCaseResidual (h : pinchRestDone_ResidualStatement.{u, w, v}) :
    PinchCase.ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hgood
  refine h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase ?_
  intro outerWalk E hnb hnd
  have hN : PinchCase.WalkDegenCaseNoninterleave b G₁ G₂ outerWalk := by
    rcases hnd with ⟨h1, h2, h3, h4⟩ | hN
    · exact witnessStepDone_noninterleave D eps X a b K hij hai hbi hab h1 h2 h3 h4 hlabel hW
        hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
    · exact hN
  have hS : ¬ FourPieceWitness.AbsorbFaceSetStepGood G₁ G₂ outerWalk := by
    rintro ⟨hs₁, hu₁, hs₂, hu₂⟩
    obtain ⟨hn1, hn2, hn3, hn4⟩ := hN
    exact hgood ⟨outerWalk, E, hnb, hn1, hn2, hn3, hn4, hs₁, hu₁, hs₂, hu₂⟩
  exact ⟨hS, pinchRestDone_exists_pinched hS⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchRestDone_pinchCaseResidual

/-- **Clause (rest) from the pinched residual** (the `_of_` reduction of lane gl-p07-68).  Cases
1 to 3 of the module docstring are proved; case 4 is the residual. -/
theorem pinchRestDone_rest_of_residual (h : pinchRestDone_ResidualStatement.{u, w, v}) :
    PinchCase.RestStatement.{u, w, v} :=
  PinchCase.rest_of_residual (pinchRestDone_pinchCaseResidual h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchRestDone_rest_of_residual

/-- **LOUD: the pinched residual from clause (rest)**, by dropping (P).  The two are equivalent as
Props; the residual is smaller only in proof content. -/
theorem pinchRestDone_residual_of_rest (h : PinchCase.RestStatement.{u, w, v}) :
    pinchRestDone_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase _
  exact h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchRestDone_residual_of_rest

/-- **P07's top target from the pinched residual alone.** -/
theorem pinchRestDone_off (h : pinchRestDone_ResidualStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  witnessStepDone_off_rest (pinchRestDone_rest_of_residual h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchRestDone_off

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
