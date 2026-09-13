# theoremc-retire lane report

Lane `theoremc-retire` (clone cs-stages) of the non-MF every-line swarm.
Updated 2026-09-13.

## Status

- First item closed. Root-imported `Manuscript/NonMF/TheoremCAssembly.lean` has no
  `sorry` (2c3c8cb40, probe `0913-013843-30184`).
- Second item closed: W3 hT6 with kh-cckw, which gave the zip-and-fold flip of
  Theorem C (e1b326ec3).
- Third item closed: Theorem C without hzip, in `TheoremCAssemblyFoldLeaf`
  (f019265bb, probe `0913-034425-9721`).
- Fourth item closed: the roster flip of `TheoremCAssemblyFoldLeaf`. hbridge and
  hfold are both closed, so `TheoremCAssemblyGreendlingerLeaf` (c5f953323, probe
  `0913-060950-64731`) states Theorem C over hgreendlinger alone.
- Current item: the one-cell connector pair of Case 1 of Lemma 9.4, meaning a backwards pair
  whose two sides are arcs of one cell.
  - The face walk is proved: `osinLemma94CaseOneWalk` (ko-closed, eb9010962 and 8f0f73966,
    probe `0913-095509-55850`).
  - On main, `osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk` proves
    `OsinLemma94CaseOneInput`. Probe `0913-093623-11190` is green on the 3292f7a20 bytes of
    Face and Run.
  - LoopCut ruling (A) is final, and it removes the competitor that Case 1 uses for one-cell
    pairs (below).
  - This lane picked A1. A2 is false, and the separate count needs the Lemma 9.7 induction
    hypothesis. Both findings went to the lead, and the ruling on the consumer is pending.
  - Hold: no edits to `OsinUnboundCaseOneFace` or `OsinUnboundCaseOneRun` until ghw-charp2
    lands census patches 01-10. As of origin 35866daf3 they have not landed.

## Landed

| SHA | what |
|---|---|
| 252c56547 | attic copies of the three edited existing modules (before the probe) |
| 4874b8162 | new `Manuscript/NonMF/TheoremCAssemblyKOLeaves.lean`, unwired (before the probe) |
| 2c3c8cb40 | normal landing after the green probe: `TheoremCAssembly`, `SeedFromTheoremC`, `SeedRemarkTheoremC`. `TheoremCAssemblyKOLeaves` is recorded as compiled; its bytes are unchanged since 4874b8162 |
| b1dc27674 | attic copy of the zip-and-fold flip of `TheoremCAssemblyKOLeaves` (before the probe) |
| e1b326ec3 | normal landing of that flip after green probe `0913-021752-29195` (base b1dc27674) |
| 84241b175, 3e9636d74, aa7391c47, a0607c71f, 1144b49f5, 9025704c3 | this report and the census row |
| f019265bb | new `Manuscript/NonMF/TheoremCAssemblyFoldLeaf.lean` (before the probe). Probe `0913-034425-9721` (base 5f9c16b7b) compiled these exact bytes (md5 a2db324a), so there was no second landing |
| c5f953323 | new `Manuscript/NonMF/TheoremCAssemblyGreendlingerLeaf.lean` (before the probe). Probe `0913-060950-64731` (base 5f789a7ba) compiled these exact bytes (md5 7dea5861), so there was no second landing |
| 8a36ad06c, 0e3aaff95 | new `Estimating/OsinLemma94CaseOneWalk.lean` and its side-kind conjuncts. Probe `0913-084930-32564` green |
| fd6ce3c09 | the walk Prop takes the connector pair over any alphabet `E`. Probe `0913-091600-31828` green on these bytes |
| 7f7ba2b4f | new `Estimating/OsinUnboundCaseOneFace.lean`. Probe `0913-090930-16094` (base 7f7ba2b4f) green on these bytes, so there was no second landing |
| 5be5cb6fc | new `Estimating/OsinUnboundCaseOneRun.lean`. Probe `0913-091600-31828` (base 7dc75e41d) green on these bytes (md5 84aa730b), so there was no second landing |
| 3292f7a20 | the same-cell split: `OsinLemma94CaseOneSameCellStatement` in Face (md5 7cb3ba81); `osinLemma94CaseOne_false_of_walk` and `osinLemma94CaseOneInput_of_walk_of_sameCell` in Run (md5 a869ccef). Probe `0913-093623-11190` green on these bytes, so there was no second landing |

## Case 1 of Lemma 9.4

`OsinLemma94CaseOneInput`: a backwards connector pair `C` of a maximal realized polygon `P`
(`C.b' < C.b`), whose target side is not a cutting path, gives `False`. Since f2cc2be97 the
connector pairs are over `symmetricLabelAlphabet D`. The proof has four pieces.

1. The face walk `OsinLemma94CaseOneWalkStatement` (8a36ad06c, 0e3aaff95, fd6ce3c09), for
   `C : WordConnectorPair E ...` over any alphabet `E`:
   - some rotation `r` of the walk of `P.face k` reads `X ++ q ++ Y ++ p⁻¹`;
   - `p` is a nonempty arc of the cell across side `C.source`, and `q` is a nonempty arc of
     the cell across `C.target` or of `∂Δ` inside one section;
   - `X` and `Y` carry the values between the corners `a'`, `b'` and `b`, `a`.

   ko-closed proved it: `osinLemma94CaseOneWalk` (`Estimating/OsinLemma94CaseOneWalkHolds.lean`,
   eb9010962 and 8f0f73966, probe `0913-095509-55850`).
2. `Estimating/OsinUnboundCaseOneFace.lean` (7f7ba2b4f, green):
   - `GFaceWordInsertion.exists_quadrilateral_region_rotate` is hull-unbound's quadrilateral
     surgery read from any rotation, on a face that may have internally paired darts.
     Its only use of the removed `NoInternalFaceDart` hypothesis was for darts of the two
     arcs, and across those lies a relator cell or the outer face
     (`faceOf_alpha_ne_of_mem_reverseDarts`, `faceOf_alpha_ne_of_mem_targetBoundaryDarts`).
     It also returns `H.target = some H.source ↔ target = some source`.
   - `RealizedSectionFamily.false_of_quadrilateral_face` is the weight contradiction on the
     family's own diagram, with no collapse step.
3. `Estimating/OsinUnboundCaseOneRun.lean` (5be5cb6fc, restructured in 3292f7a20):
   - `osinLemma94CaseOne_false_of_walk` handles one pair for `ε ≥ 3`. The connectors are
     respelled nonempty by `WordConnectorPair.exists_nonempty_connectors`.
   - `osinLemma94CaseOneInput_of_walk (hwalk) : OsinLemma94CaseOneInput`, with `ε₀ = 3` and
     `ρ₀ = 1`. It relies on the current `RespectsSections`.
4. The same-cell split (3292f7a20):
   - `OsinLemma94CaseOneSameCellStatement` (in Face) is `OsinLemma94CaseOneInput` with the extra
     hypothesis `P.kind k C.source = P.kind k C.target`.
   - `osinLemma94CaseOneInput_of_walk_of_sameCell (hwalk) (hsame) : OsinLemma94CaseOneInput`,
     with `ε₀ = max 3 ε₁`, uses the walk only when the two kinds differ.

### LoopCut ruling (A), final

- `RespectsSections` gains `target ≠ some source` as its first conjunct, so a region from a cell
  to itself is not a candidate.
- ghw-charp2 lands census patches 01-10 as one landing. For this lane's files:
  - patch 09(d)/(e) adds `hloop : target ≠ some source` to `exists_quadrilateral_region_rotate`
    and `false_of_quadrilateral_face`;
  - patch 10(f) adds `hkind : P.kind k C.source ≠ P.kind k C.target` to
    `osinLemma94CaseOne_false_of_walk`, derives `hloop` from the side-kind conjuncts of the walk,
    and deletes `osinLemma94CaseOneInput_of_walk`.
- So after the landing, audit-sec3's note that `OsinLemma94CaseOneSameCellStatement` is redundant
  no longer holds: the one-cell pair has no competitor region.

### The one-cell pair (this lane's item)

The lead offered A1 (a premise in `OsinLemma94CaseOneInput`, with one-cell pairs counted
separately) or A2 (a polygon field). This lane picked A1.

- **A1 premise.** `P.kind k C.target ≠ P.kind k C.source`. It is the hypothesis `hkind` of
  patch 10(f), so after the landing `osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk`
  proves the new `OsinLemma94CaseOneInput`.
- **A2 is false.** A field that forbids two sides on one cell fails whenever an unselected
  `G`-face touches a cell along two short arcs with the arc of another cell between them.
  `Maximal`, `DartMinimal` and least area all allow that.
- **What remains.** The two sides are arcs `p`, `q` of one cell, and both walk portions between
  them have short value. One of the two pockets bounded by a walk portion and a subarc of the
  cell is bounded.
  - Pocket without an R-cell: refutable from the hypotheses of Lemma 9.4, modulo a planar pocket
    lemma. `NoLoops` (from `S.respects` under (A)) leaves no selected region inside, and
    `gFacesApart_of_dartMinimal` no other unselected `G`-face. So the walk portion is arcs of the
    cell plus spurs, and `PendantPathRemovalInput` against `DartMinimal`, or `Maximal` at a
    junction without a spur, refutes it.
  - Pocket with an R-cell: Osin's loop case ("the subdiagram `Ξ` will be bounded by `st`"). The
    pocket, with the subarc and a connector as its two sections, is an `OsinLoopCut`, and
    `OsinLoopCut.false_of_below` refutes it given `OsinLemma97Below ... Delta.rCellCount`.
- **The count.** No true instance has a one-cell pair, but the second case needs the induction
  hypothesis. A count Prop without it is as hard as Lemma 9.7 on smaller diagrams. A count over
  all sides on a repeated cell is false, since a face may wrap a cell along two arcs with a
  long-valued walk between them.
- **Options sent to the lead.**
  - (i) Rule 22: `OsinLemma94SectionStatement` and `UnboundInput` gain `OsinLemma97Below` at
    `Delta.rCellCount`. The one real call site (`OsinAppendixSectionInduction.lean:208`) has
    `hbelow` in scope (l.167), and the lifts in `OsinAppendixAssembly` and
    `OsinAppendixLemma97Pocket` pass it through. PlanarPieces then gains
    `OsinLemma94CaseOneOneCellInput`, and the consumer splits Case 1 on the kind.
    `OsinLemma97bConclusion` is defined after `OsinLemma94SectionStatement` in
    `OsinAppendixSections.lean`, so the binder is spelled inline or the definition moves up.
  - (ii) Keep the statements, so the one-cell pair stays a named hypothesis of PlanarPieces, which
    leaves hgreendlinger conditional on it.
  - This lane recommends (i). Its new module would hold the cell-free pocket and the
    `OsinLoopCut` construction. `OsinAppendixSectionMultipleEdge` imports no Lemma 9.4 module,
    so there is no import cycle.

## Theorem C without hzip, and over hgreendlinger alone

`TheoremCAssemblyFoldLeaf` (f019265bb, green):
- `TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaFold` and
  `TheoremC.manuscriptTorsionFreeSimplified_of_leastAreaFold` take `hgreendlinger`,
  `hbridge` and `hfold : ∀ (V : Type) (X : Systolic.TriangleComplex V),
  Systolic.MirrorFoldStatement X`.
- They apply the `_of_leastAreaZipFold` forms of `TheoremCAssemblyKOLeaves` at
  `hzip := KMSGroup.CCKW.zipSpur_cosetComplex` (8389a0e6c), with hfold used at
  `CCKW.cosetComplex`.
- Wire-queue line added.

`TheoremCAssemblyGreendlingerLeaf` (c5f953323, green):
- `TheoremC.manuscriptTorsionFreeFullMFRadical_of_greendlinger` and
  `TheoremC.manuscriptTorsionFreeSimplified_of_greendlinger` take `hgreendlinger`
  alone. Both `#audit_axioms` lines passed.
- They apply the `_of_leastAreaFold` forms at
  `hbridge := HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`
  (hull-bridge, 18682110d) and `hfold := fun _ X => Systolic.mirrorFold X`
  (fff-periodic, 426813b24).
- Wire-queue line added. Wire it after `TheoremCAssemblyFoldLeaf`,
  `GGT.HullSCLemma51EmbeddedBridgeHolds` and `GGT.SystolicDiscMirrorFold`, all
  three queued.

## What changed in the first item

Deleted from `TheoremCAssembly` (no file was deleted):
- the four unconsumed sorry declarations `estimatingSelectionConstruction`,
  `estimatingUnboundOutput`, `relativeIsoperimetricBridgeQuasiGeodesic` and
  `hullRelatorRespelling`, and the chain that consumed them;
- the `kotowskiOllivier` sorry, with `smallCancellationQuotient`,
  `hullCommonQuotient` and `literatureInputs`;
- both `_openAdmissions` endpoints.

Added:
- `TorsionFree.hullTheorem71_of_leastAreaLeaves` and
  `TorsionFree.hullInputs_of_leastAreaLeaves`.
- `TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs` and
  `TheoremC.manuscriptTorsionFreeSimplified_of_leastAreaInputs`, over
  `hgreendlinger`, `hbridge` and `hKO`, with no simple-group binder.
- `TheoremCAssemblyKOLeaves`: the `_of_leastAreaKOLeaves` forms (hzip, hfold, hT6)
  and, after W3, the `_of_leastAreaZipFold` forms (hzip, hfold).
- `MFRecognition.SeedFromTheoremC.E` is chosen from
  `manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs` and takes the three
  hypotheses explicitly.

Rule 22: every Lean importer of `TheoremCAssembly` went into the probe.
`scripts/TheoremCCompletionAudit.lean` is not a module.

## Residual Props (exact)

- `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`
  (hgreendlinger; hull-respell and W1). It is the only binder of the
  `_of_greendlinger` forms of Theorem C.
- Inside W1 h94, for this lane's item:
  - On main, none: `osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk` proves
    `OsinLemma94CaseOneInput`, but no landed declaration composes them. The composition is held,
    because patch 10(f) deletes `_of_walk`.
  - After patches 01-10: the one-cell pair, today the named hypothesis
    `GGT.VanKampen.OsinLemma94CaseOneSameCellStatement`. Its replacement, including whether
    Lemma 9.4 takes `OsinLemma97Below`, waits on the lead's ruling.
- Closed walls: hbridge, hzip, hfold, hT6, and hKO (f65f99f17).

## Census

`metadata/nm-census-rows/theoremc-retire.tsv` has one row, LINE:284, graded
`partial`. Its carriers are the `_of_leastAreaInputs`, `_of_leastAreaKOLeaves`,
`_of_leastAreaZipFold`, `_of_leastAreaFold` and `_of_greendlinger` endpoints (10
declarations). Its note retires the baseline finding "root-imported
TheoremCAssembly has 5 sorries" (census2 U2). The grade stays `partial` while
hgreendlinger is open. There is no Case 1 row yet, since it waits for the composed endpoint.

## Stale references

One item remains: nothing supplies `HullSC.HullRelatorRespellingStatement`. It is still the
binder `hrespell` at `GGT/HullSCLemma44FamilyAssembly.lean:548, 655, 670`,
`GGT/HullSCLemma44QuasiGeodesicBridge.lean:412, 476` and
`GGT/HullSCLemma44RespellingBinders.lean:229`.

## Next

- On the lead's ruling:
  - draft the PlanarPieces statement patch (A1 premise, the one-cell Prop, the consumer split)
    and send it to hull-unbound, rebased after hull-count94's F1 landing;
  - prove the cell-free pocket and the `OsinLoopCut` construction in a new module.
- When ghw-charp2 reports patches 01-10 landed:
  - land the composed Case 1 endpoint in the A1 form, then add a wire-queue line and a census row.
- Offered to the lead: once GreendlingerLeaf is wired, re-point `SeedFromTheoremC.E` at
  `_of_greendlinger` (rule 22: probe `SeedRemarkTheoremC` with it).
- One-application flip, this lane: once hgreendlinger closes, the `_of_greendlinger`
  forms become closed Theorem C, and LINE:284 can be regraded.
