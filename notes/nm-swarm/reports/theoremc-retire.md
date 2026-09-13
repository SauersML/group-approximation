# theoremc-retire lane report

Lane `theoremc-retire` (clone cs-stages) of the non-MF every-line swarm.
Updated 2026-09-13 ~14:45.

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
    `OsinLemma94CaseOneInput` (probe `0913-093623-11190` on the 3292f7a20 bytes of Face and Run).
    No landed declaration composes them.
  - Rulings on the one-cell pair:
    - Roster 705-707: option (i). Lemma 9.4 takes `OsinLemma97Below … Delta.rCellCount`, the
      inductive assumption. The landing order is (A), then F1, then this lane's threading T.
    - 13:40: patch 10(f)'s deletion is overruled. After (A), `osinLemma94CaseOneInput_of_walk`
      takes `hsame : OsinLemma94CaseOneSameCellStatement`.
    - 14:05: ko-closed's (1) wins, the metric kill at the printed threshold.
      - The `λ⁻¹(ε + c)` respelling is cancelled, including hull-unbound's Dense draft. So this
        lane's `OsinLemma94CaseOneOneCellInput` and its consumer split (old blocks OC1-OC5) are
        withdrawn.
      - jacobson owns the producer of `OsinLemma94CaseOneSameCellStatement`. It composes
        ko-closed's kill (cell-free pocket) with `nonempty_osinLoopCut_of_pocketRegion`
        (70f8cd913, pocket with a relator cell), and refutes the loop cut by the inductive
        assumption.
      - T stays with this lane as its own co-probed landing after (A). The owners get hold
        notices, and each file's origin blob is checked at push. Assembly and Lemma97Pocket, which
        no lane lists, join this lane's files for that landing.
  - State of (A): not landed at origin afe0638dd (`RespectsSections` unchanged).
    - ghw-charp2's co-probe `0913-135734-55169` failed (rc=1) at 14:03. The rulings-1410 roster
      draft calls it GREEN, but the record's status line says FAILED.
    - Its re-probes `0913-143304-32295` (base b590ad02a) and `0913-144048-88101` (base afe0638dd,
      14:44) are GREEN on the same bytes: Sections c1b41109, SectionInduction 5c582de9,
      GreendlingerParts 210b5295, Face a0dd5b3f, Run f598845e.
    - The staged Face keeps the binders of `OsinLemma94CaseOneSameCellStatement`, now at
      l.474-492.
    - The staged Run is this lane's OC6 shape: `false_of_walk` takes `hkind`, `_of_walk` takes
      `hsame`, and `_of_walk_of_sameCell` stays as an alias.
  - F1 (hull-count94) is landed (9f8779c4e).
  - Hold: no edits to `OsinUnboundCaseOneFace` or `OsinUnboundCaseOneRun` until ghw-charp2
    reports (A) landed.
  - Sent (~14:20):
    - jacobson answers its 13:16 question:
      - the SameCell spelling (staged Face l.474-492; patches 09(d)/(e) do not change its binders);
      - T's binder;
      - the names for the refutation: `OsinLoopCut.false_of_below`, `o52LeastArea`,
        `exists_rho_widthBudget`.
    - ko-closed: OneCellInput is withdrawn, so the OneCellMorse kills now feed jacobson's
      producer.
    - hull-unbound: OC1-OC5 are withdrawn. T now changes the statement of
      `OsinLemma94CaseOneInput` and the consumer at l.471 and l.485. A hold notice follows at probe
      time.
  - Sent (14:44): jacobson, the T names for hbelow in its producer.
    - After T, the binder of `OsinLemma94CaseOneSameCellStatement` matches fff-periodic's
      `OsinLemma94SameCellPocketInput` (OsinUnboundSameCellPocket:47) token for token, so hbelow
      passes to fff-periodic's shared kill by `exact`.
    - The direct refutation is `cut.false_of_below o52LeastArea hcondition hlambda hmu hmuUpper
      hrho hlarge hlea (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos
      cut.rCellCount_lt)`, with `hlarge` from `exists_rho_widthBudget`.
  - Residual Props owned by this lane: none new (see Residual Props below).

## The threading T (replayable, dry run clean, not probed)

- Draft: `$NM/backup/theoremc-retire/threading-option-i-draft.lean.txt`, blocks T1-T8.
- Replay script: `$NM/backup/theoremc-retire/apply-T.py OUTDIR [--rev REV] [--overlay DIR]`.
  - Each edit asserts its occurrence count, and every new line is at most 100 characters.
  - On any mismatch it writes nothing.
- Dry run (14:34), on origin e4f96af1e with ghw-charp2's staged (A) bytes as overlay: rc=0.
  `T-candidates-dry/T.diff` (304 lines) is reviewed.
- Gate script `T-prep.sh`, run once (A) is on main:
  - it checks that each tree file equals its origin blob;
  - it reruns the replay on origin and compares the result with the dry run;
  - it backs up the tree files and adds the edited paths to this lane's file list.
- At origin afe0638dd, the tree equals origin in all fifteen T files except the five (A) files.

- T1 Sections: `OsinLemma97bConclusion` moves above l.284, and `OsinLemma94SectionStatement`
  (l.303) gains the inductive assumption after `0 < Delta.rCellCount`.
- T2 SectionInduction: `UnboundInput` gains `mu` and `OsinLemma97Below … Delta.rCellCount`. l.148
  gains `mu`, and l.208 passes `hbelow` (in scope from l.167).
- T3 DescentInduction: `mu` at l.55, l.133 and l.243; `hbelow` at l.101.
- T4 Assembly l.125-127 and Lemma97Pocket l.81-83: the lifts pass `hbelow`.
- T5 Counting l.100 and Pieces l.237: the intro gains `_hbelow`.
- T6 PlanarPieces:
  - `OsinLemma94CaseOneInput` (l.395) gains the binder after l.405;
  - the consumer's intro (l.471) gains `hbelow` and passes it to `honeRho` at l.485.
- T7 Face: `OsinLemma94CaseOneSameCellStatement` gains the binder (staged l.484).
- T8 Run: `_of_walk`'s intro (staged l.93) and same-kind branch (staged l.95) pass `hbelow`.

In PlanarPieces and Face the binder is spelled out, since neither module reaches
`OsinAppendixSectionInduction`. By definition it is
`OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount`. SectionResiduals needs no
term change.

- Co-probe (Rule 22): Sections, SectionInduction, DescentInduction, Assembly, Lemma97Pocket,
  Counting, Pieces, PlanarPieces, SectionResiduals, GreendlingerParts, GreendlingerPocketParts,
  Face, Run, plus DescentResiduals (dgo-analytic, 5be777f16, passes `h94` through) and CaseTwo
  (imports Face).
- Owners of the edited files:
  - ghw-charp2 and hull-select: Sections, SectionInduction;
  - dgo-analytic and hull-select: DescentInduction;
  - hull-count94: Counting, Pieces, PlanarPieces;
  - hull-unbound: Pieces, PlanarPieces;
  - ghw-charp2 and this lane: Face, Run;
  - no owner, so they join this lane's files: Assembly, Lemma97Pocket.

  Probed, not edited: GreendlingerParts (ghw-charp2), GreendlingerPocketParts (hull-respell),
  SectionResiduals (hull-unbound), DescentResiduals (dgo-analytic), CaseTwo (sec5-sentences).

## Landed

| SHA | what |
|---|---|
| 252c56547 | attic copies of the three edited existing modules (before the probe) |
| 4874b8162 | new `Manuscript/NonMF/TheoremCAssemblyKOLeaves.lean`, unwired (before the probe) |
| 2c3c8cb40 | normal landing after the green probe: `TheoremCAssembly`, `SeedFromTheoremC`, `SeedRemarkTheoremC`. `TheoremCAssemblyKOLeaves` is recorded as compiled; its bytes are unchanged since 4874b8162 |
| b1dc27674 | attic copy of the zip-and-fold flip of `TheoremCAssemblyKOLeaves` (before the probe) |
| e1b326ec3 | normal landing of that flip after green probe `0913-021752-29195` (base b1dc27674) |
| 84241b175, 3e9636d74, aa7391c47, a0607c71f, 1144b49f5, 9025704c3, b401d6d3d, 32643dcc6 | this report and the census row |
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
   - On main, `osinLemma94CaseOneInput_of_walk (hwalk) : OsinLemma94CaseOneInput`, with `ε₀ = 3`
     and `ρ₀ = 1`, relies on the current `RespectsSections`.
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
  - OC6, this lane's Run patch, rides in (A): `osinLemma94CaseOne_false_of_walk` gains
    `hkind : P.kind k C.source ≠ P.kind k C.target` and derives `hloop` from the side-kind
    conjuncts of the walk, and `osinLemma94CaseOneInput_of_walk` takes `hsame` (patch 10(f)'s
    deletion is overruled).
- So after the landing, audit-sec3's note that `OsinLemma94CaseOneSameCellStatement` is redundant
  no longer holds: the one-cell pair has no competitor region.

### The one-cell pair

- **A1 premise** (this lane's pick). `P.kind k C.target ≠ P.kind k C.source` is `hkind` in OC6.
- **A2 is false.** A field that forbids two sides on one cell fails whenever an unselected
  `G`-face touches a cell along two short arcs with the arc of another cell between them.
  `Maximal`, `DartMinimal` and least area all allow that.
- **What remains.** The two sides are arcs `p`, `q` of one cell, and both walk portions between
  them have short value. One of the two pockets bounded by a walk portion and a subarc of the
  cell is bounded.
  - Pocket without an R-cell: ko-closed's metric kill (ruling (1)), over
    `OsinLemma94OneCellValue` (ea9016135, 36524dbf0) and the OneCellMorse module in progress.
  - Pocket with an R-cell: Osin's loop case. jacobson's `nonempty_osinLoopCut_of_pocketRegion`
    gives an `OsinLoopCut`, and `OsinLoopCut.false_of_below` refutes it given the inductive
    assumption, which T supplies.
  - Not owned by this lane: the PocketRegion from the Case 1 walk decomposition. Neither ko-closed
    nor jacobson has a producer on main for it.
- **The count.** No true instance has a one-cell pair, but the second case needs the induction
  hypothesis. A count Prop without it is as hard as Lemma 9.7 on smaller diagrams. A count over
  all sides on a repeated cell is false, since a face may wrap a cell along two arcs with a
  long-valued walk between them.

### Gap finding (roster l.786, l.849)

- `false_of_quadrilateral_face` and the walk Prop's conclusion need `sourceArc.reverseDarts` to
  be a literal piece of the face walk, with the junction values pinned to the connector endpoints.
- Take a class-word pair whose `[a, a']` or `[b', b]` strictly contains a gap: a bubble of Π,
  whose reversed darts lie on inner faces, or a hair of the face. That pair has no split the user
  accepts. So Case 1 on class words needs the walk to avoid such pairs, or the opening surgeries
  (l.850).
- hull-unbound is model-testing this finding. The verdict goes to ko-closed and this lane.
- The wrap-pair note (l.825) does not touch Case 1: neither `false_of_walk` nor the walk Prop
  takes `P.Maximal`.

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
  - On main, none new: `osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk` proves
    `OsinLemma94CaseOneInput`, but no landed declaration composes them.
  - After (A): `GGT.VanKampen.OsinLemma94CaseOneSameCellStatement`, the binder `hsame` of
    `osinLemma94CaseOneInput_of_walk`. jacobson owns its producer. After T it carries the
    inductive assumption.
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

- When (A) is on main:
  - run `T-prep.sh`: origin-blob gate, replay on origin, backup, lane file list (Assembly and
    Lemma97Pocket included);
  - send hold notices to ghw-charp2, hull-select, dgo-analytic, hull-count94 and hull-unbound, and
    announce the window in wire-queue.txt;
  - run one background probe over the co-probe set, check each file's origin blob at push, land,
    then update this report and the census.
- After jacobson's producer lands: the composed endpoint
  `osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk <producer>`, a wire-queue line and a
  census row.
- Offered to the lead: once GreendlingerLeaf is wired, re-point `SeedFromTheoremC.E` at
  `_of_greendlinger` (Rule 22: probe `SeedRemarkTheoremC` with it).
- One-application flip, this lane: once hgreendlinger closes, the `_of_greendlinger`
  forms become closed Theorem C, and LINE:284 can be regraded.
