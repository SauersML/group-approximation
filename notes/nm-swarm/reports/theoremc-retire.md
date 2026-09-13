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
- Current item: `OsinLemma94CaseOneInput`, Case 1 of Lemma 9.4 (hull-unbound's
  `Estimating/OsinLemma94PlanarPieces.lean`). It now reduces to one Prop, the face walk
  `OsinLemma94CaseOneWalkStatement`, and ko-closed is proving that Prop. Probe
  `0913-091600-31828` (base 7dc75e41d) is green on the landed bytes of all three new
  modules.

## Landed

| SHA | what |
|---|---|
| 252c56547 | attic copies of the three edited existing modules (before the probe) |
| 4874b8162 | new `Manuscript/NonMF/TheoremCAssemblyKOLeaves.lean`, unwired (before the probe) |
| 2c3c8cb40 | normal landing after the green probe: `TheoremCAssembly`, `SeedFromTheoremC`, `SeedRemarkTheoremC`. `TheoremCAssemblyKOLeaves` is recorded as compiled; its bytes are unchanged since 4874b8162 |
| b1dc27674 | attic copy of the zip-and-fold flip of `TheoremCAssemblyKOLeaves` (before the probe) |
| e1b326ec3 | normal landing of that flip after green probe `0913-021752-29195` (base b1dc27674) |
| 84241b175, 3e9636d74, aa7391c47, a0607c71f, 1144b49f5 | this report and the census row |
| f019265bb | new `Manuscript/NonMF/TheoremCAssemblyFoldLeaf.lean` (before the probe). Probe `0913-034425-9721` (base 5f9c16b7b) compiled these exact bytes (md5 a2db324a), so there was no second landing |
| c5f953323 | new `Manuscript/NonMF/TheoremCAssemblyGreendlingerLeaf.lean` (before the probe). Probe `0913-060950-64731` (base 5f789a7ba) compiled these exact bytes (md5 7dea5861), so there was no second landing |
| 8a36ad06c, 0e3aaff95 | new `Estimating/OsinLemma94CaseOneWalk.lean` and its side-kind conjuncts. Probe `0913-084930-32564` green |
| fd6ce3c09 | the walk Prop takes the connector pair over any alphabet `E`. Probe `0913-091600-31828` green on these bytes |
| 7f7ba2b4f | new `Estimating/OsinUnboundCaseOneFace.lean`. Probe `0913-090930-16094` (base 7f7ba2b4f) green on these bytes, so there was no second landing |
| 5be5cb6fc | new `Estimating/OsinUnboundCaseOneRun.lean`. Probe `0913-091600-31828` (base 7dc75e41d) green on these bytes (md5 84aa730b), so there was no second landing |

## Case 1 of Lemma 9.4

`OsinLemma94CaseOneInput`: a backwards connector pair `C` of a maximal realized polygon `P`
(`C.b' < C.b`), whose target side is not a cutting path, gives `False`. Since f2cc2be97 the
connector pairs are over `symmetricLabelAlphabet D`. The proof has three pieces.

1. The face walk `OsinLemma94CaseOneWalkStatement` (8a36ad06c, 0e3aaff95, fd6ce3c09), for
   `C : WordConnectorPair E ...` over any alphabet `E`:
   - some rotation `r` of the walk of `P.face k` reads `X ++ q ++ Y ++ p⁻¹`;
   - `p` is a nonempty arc of the cell across side `C.source`, and `q` is a nonempty arc of
     the cell across `C.target` or of `∂Δ` inside one section;
   - `X` and `Y` carry the values between the corners `a'`, `b'` and `b`, `a`.
   **ko-closed is proving it** (`theorem osinLemma94CaseOneWalk`, own module).
2. `Estimating/OsinUnboundCaseOneFace.lean` (7f7ba2b4f, green):
   - `GFaceWordInsertion.exists_quadrilateral_region_rotate` is hull-unbound's quadrilateral
     surgery read from any rotation, on a face that may have internally paired darts.
     Its only use of the removed `NoInternalFaceDart` hypothesis was for darts of the two
     arcs, and across those lies a relator cell or the outer face
     (`faceOf_alpha_ne_of_mem_reverseDarts`, `faceOf_alpha_ne_of_mem_targetBoundaryDarts`).
     It also returns `H.target = some H.source ↔ target = some source`.
   - `RealizedSectionFamily.false_of_quadrilateral_face` is the weight contradiction on the
     family's own diagram, with no collapse step.
3. `Estimating/OsinUnboundCaseOneRun.lean` (5be5cb6fc):
   `osinLemma94CaseOneInput_of_walk (hwalk : OsinLemma94CaseOneWalkStatement.{u,w,v}) :
   OsinLemma94CaseOneInput.{u,w,v}`, with `ε₀ = 3` and `ρ₀ = 1`. The connectors are
   respelled nonempty by `WordConnectorPair.exists_nonempty_connectors`.

LoopCut gate (answer sent to main). Case 1 does not force a same-cell competitor, but it
admits one: both sides can be arcs of one cell. Under the current `RespectsSections` the
proof above covers that subcase. Under the provisional ruling (A) (`target ≠ some source`)
the new region is legal only when `P.kind k C.source ≠ P.kind k C.target`. The same-cell
subcase would then need its own argument or a hypothesis in `OsinLemma94CaseOneInput`.
Waiting for the lead's ruling.

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
- Inside W1 h94, for this lane's item: `OsinLemma94CaseOneWalkStatement` (ko-closed), and the
  lead's LoopCut ruling.
- Closed walls: hbridge, hzip, hfold, hT6, and hKO (f65f99f17).

## Census

`metadata/nm-census-rows/theoremc-retire.tsv` has one row, LINE:284, graded
`partial`. Its carriers are the `_of_leastAreaInputs`, `_of_leastAreaKOLeaves`,
`_of_leastAreaZipFold`, `_of_leastAreaFold` and `_of_greendlinger` endpoints (10
declarations). Its note retires the baseline finding "root-imported
TheoremCAssembly has 5 sorries" (census2 U2). The grade stays `partial` while
hgreendlinger is open. There is no Case 1 row yet; it waits for the walk proof.

## Stale references

One item remains: nothing supplies `HullSC.HullRelatorRespellingStatement`. It is still the
binder `hrespell` at `GGT/HullSCLemma44FamilyAssembly.lean:548, 655, 670`,
`GGT/HullSCLemma44QuasiGeodesicBridge.lean:412, 476` and
`GGT/HullSCLemma44RespellingBinders.lean:229`.

## Next

- When ko-closed lands `osinLemma94CaseOneWalk`: add `osinLemma94CaseOneInput_closed` to
  `OsinUnboundCaseOneRun`, probe it, then add a wire-queue line and a census row.
- If ruling (A) lands: handle the same-cell subcase, through the `hHloop` output of
  `exists_quadrilateral_region_rotate` and the side-kind conjuncts of the walk.
- Offered to the lead: once GreendlingerLeaf is wired, re-point `SeedFromTheoremC.E` at
  `_of_greendlinger` (rule 22: probe `SeedRemarkTheoremC` with it).
- One-application flip, this lane: once hgreendlinger closes, the `_of_greendlinger`
  forms become closed Theorem C, and LINE:284 can be regraded.
