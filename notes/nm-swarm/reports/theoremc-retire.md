# theoremc-retire lane report

Lane `theoremc-retire` (clone cs-stages) of the non-MF every-line swarm.
Updated 2026-09-13 ~15:08.

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
- Current item: the one-cell connector pair of Case 1 of Lemma 9.4, meaning a backwards pair whose
  two sides are arcs of one cell. The threading T is landed (48c6cc71e, probe `0913-145812-91168`).
  - The face walk is proved: `osinLemma94CaseOneWalk` (ko-closed, eb9010962 and 8f0f73966,
    probe `0913-095509-55850`).
  - After (A), `osinLemma94CaseOneInput_of_walk` takes `hsame : OsinLemma94CaseOneSameCellStatement`.
    ghw-assembly's waist `OsinGreendlingerOpenResiduals` (5f031e3a6) composes
    `osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk hsameOne`.
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
    - rulings-1410: T lands regardless of ko-closed's pick. fff-periodic owns the shared kill
      "relator-cell pocket plus hbelow gives False", which jacobson's R-cell branch consumes.
  - (A) is landed: ghw-charp2 f04929ebb (14:49:30), after re-probe `0913-144048-88101` (GREEN,
    base afe0638dd).
    - Correction: its first co-probe `0913-135734-55169` failed (rc=1) at 14:03. The rulings-1410
      roster draft calls it GREEN, but the record's status line says FAILED.
    - Face and Run after (A): `false_of_walk` takes `hkind`, `_of_walk` takes `hsame`, and
      `_of_walk_of_sameCell` stays as an alias.
    - The hold on this lane's Face and Run edits is lifted.
  - F1 (hull-count94) is landed (9f8779c4e).
  - Sent (~14:20):
    - jacobson answers its 13:16 question:
      - the SameCell spelling (patches 09(d)/(e) do not change its binders);
      - T's binder;
      - the names for the refutation: `OsinLoopCut.false_of_below`, `o52LeastArea`,
        `exists_rho_widthBudget`.
    - ko-closed: OneCellInput is withdrawn, so the OneCellMorse kills now feed jacobson's
      producer.
    - hull-unbound: OC1-OC5 are withdrawn. T changes the statement of `OsinLemma94CaseOneInput`
      and its consumer in PlanarPieces.
  - Sent (14:44): jacobson, the T names for hbelow in its producer.
    - After T, the binder of `OsinLemma94CaseOneSameCellStatement` matches fff-periodic's
      `OsinLemma94SameCellPocketInput` (OsinUnboundSameCellPocket:47) token for token, so hbelow
      passes to fff-periodic's shared kill by `exact`.
    - The direct refutation is `cut.false_of_below o52LeastArea hcondition hlambda hmu hmuUpper
      hrho hlarge hlea (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos
      cut.rCellCount_lt)`, with `hlarge` from `exists_rho_widthBudget`.
  - Sent (14:55):
    - hold notices to ghw-charp2, hull-select, dgo-analytic, hull-count94 and hull-unbound, with
      the window line in wire-queue.txt;
    - ko-closed: coordinate case (a) with jacobson, who owns the producer;
    - fff-periodic: the hbelow binder for `OsinLemma94PolygonCountInput` and
      `OsinLemma94PolygonCoversInput` is not in T. It is a follow-on co-probe after T lands (owners
      hull-count94, hull-unbound, ghw-assembly, hull-respell), and main rules on who runs it.
  - Sent (15:00): ghw-assembly, the probe already covers its waist bytes (md5 b06afa2f), and T keeps
    the argument lists of `_of_walk` and `osinLemma94Section_of_residuals`.
  - Residual Props owned by this lane: none new (see Residual Props below).

## The threading T (landed 48c6cc71e)

- Draft: `$NM/backup/theoremc-retire/threading-option-i-draft.lean.txt`, blocks T1-T8.
- Replay script: `$NM/backup/theoremc-retire/apply-T.py OUTDIR [--rev REV] [--overlay DIR]`.
  - Each edit asserts its occurrence count, and every new line is at most 100 characters.
  - On any mismatch it writes nothing.
- Dry run (14:34), on origin e4f96af1e with ghw-charp2's staged (A) bytes as overlay: rc=0.
  `T-candidates-dry/T.diff` (304 lines) is reviewed.
- Gate `T-prep.sh` passed at origin d60f40599 (PREP OK): each tree file equals its origin blob, the
  replay on origin equals the dry run, the tree bytes are backed up in `pre-T/`, and the edited
  paths are in this lane's file list.
- Re-gate at origin eeef4bc37, just before the copy: all ten bases unchanged in origin and tree.
  The candidate md5s are verified in the tree.
- Probe `0913-145812-91168`: base 88fc580eb, overlay 17 files, 16 modules, GREEN. The record's
  evidence lists all ten candidate md5s.
- Landed 48c6cc71e (parent 1eeac4b57) through `T-land.sh --land`. The gate re-checked the record
  verdict, each edited file's origin md5 against its base, the tree bytes against the candidates,
  and that no probed module moved since the probe base. The first push lost a ref race
  (`cannot lock ref`) and landed nothing; the retry landed.

- T1 Sections: `OsinLemma97bConclusion` moves above Lemma 9.4, and `OsinLemma94SectionStatement`
  gains the inductive assumption after `0 < Delta.rCellCount`.
- T2 SectionInduction: `UnboundInput` gains `mu` and `OsinLemma97Below … Delta.rCellCount`. The
  h94 binder gains `mu`, and the call passes `hbelow`.
- T3 DescentInduction: three h94 binders gain `mu`; one call passes `hbelow`.
- T4 Assembly and Lemma97Pocket: the lifts pass `hbelow`.
- T5 Counting and Pieces: the intro gains `_hbelow`.
- T6 PlanarPieces: `OsinLemma94CaseOneInput` gains the binder; the consumer's intro gains `hbelow`
  and passes it to `honeRho`.
- T7 Face: `OsinLemma94CaseOneSameCellStatement` gains the binder.
- T8 Run: `_of_walk`'s intro and same-kind branch pass `hbelow`.

MANIFEST (md5 base → candidate): Sections c1b41109→846d51ce, SectionInduction 5c582de9→e11ff35a,
DescentInduction 7ca5d334→0ee403c7, Assembly 9da48cab→f8110417, Lemma97Pocket 28de77e9→be894021,
Counting 7921f7fa→ac735a2f, Pieces b472c7dc→7b585512, PlanarPieces 1999698a→8ca770a0,
Face a0dd5b3f→cf0aaccf, Run f598845e→b23409cc.

In PlanarPieces and Face the binder is spelled out, since neither module reaches
`OsinAppendixSectionInduction`. By definition it is
`OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount`. SectionResiduals needs no
term change.

- Co-probe (Rule 22): Sections, SectionInduction, DescentInduction, Assembly, Lemma97Pocket,
  Counting, Pieces, PlanarPieces, SectionResiduals, GreendlingerParts, GreendlingerPocketParts,
  Face, Run, DescentResiduals (passes `h94` through), CaseTwo (imports Face) and
  GreendlingerOpenResiduals (5f031e3a6, passes `hsameOne` through `_of_walk`).
- Rule 22 re-grep at d60f40599: the hits in AssemblyDescent, AntiparallelMetric, RunInput and
  UnboundSameCellPocket are docstrings. DescentCut's `OsinLemma97Below.mono` is untouched, since
  the definition of `OsinLemma97Below` does not change.
- Owners of the edited files:
  - ghw-charp2 and hull-select: Sections, SectionInduction;
  - dgo-analytic and hull-select: DescentInduction;
  - hull-count94: Counting, Pieces, PlanarPieces;
  - hull-unbound: Pieces, PlanarPieces;
  - ghw-charp2 and this lane: Face, Run;
  - no owner, so they join this lane's files: Assembly, Lemma97Pocket.

  Probed, not edited: GreendlingerParts (ghw-charp2), GreendlingerPocketParts (hull-respell),
  SectionResiduals (hull-unbound), DescentResiduals (dgo-analytic), CaseTwo (sec5-sentences),
  GreendlingerOpenResiduals (ghw-assembly).

## Landed

| SHA | what |
|---|---|
| 252c56547 | attic copies of the three edited existing modules (before the probe) |
| 4874b8162 | new `Manuscript/NonMF/TheoremCAssemblyKOLeaves.lean`, unwired (before the probe) |
| 2c3c8cb40 | normal landing after the green probe: `TheoremCAssembly`, `SeedFromTheoremC`, `SeedRemarkTheoremC`. `TheoremCAssemblyKOLeaves` is recorded as compiled; its bytes are unchanged since 4874b8162 |
| b1dc27674 | attic copy of the zip-and-fold flip of `TheoremCAssemblyKOLeaves` (before the probe) |
| e1b326ec3 | normal landing of that flip after green probe `0913-021752-29195` (base b1dc27674) |
| 84241b175, 3e9636d74, aa7391c47, a0607c71f, 1144b49f5, 9025704c3, b401d6d3d, 32643dcc6, d4062cdf1, d8e7335b7 | this report and the census row |
| f019265bb | new `Manuscript/NonMF/TheoremCAssemblyFoldLeaf.lean` (before the probe). Probe `0913-034425-9721` (base 5f9c16b7b) compiled these exact bytes (md5 a2db324a), so there was no second landing |
| c5f953323 | new `Manuscript/NonMF/TheoremCAssemblyGreendlingerLeaf.lean` (before the probe). Probe `0913-060950-64731` (base 5f789a7ba) compiled these exact bytes (md5 7dea5861), so there was no second landing |
| 8a36ad06c, 0e3aaff95 | new `Estimating/OsinLemma94CaseOneWalk.lean` and its side-kind conjuncts. Probe `0913-084930-32564` green |
| fd6ce3c09 | the walk Prop takes the connector pair over any alphabet `E`. Probe `0913-091600-31828` green on these bytes |
| 7f7ba2b4f | new `Estimating/OsinUnboundCaseOneFace.lean`. Probe `0913-090930-16094` (base 7f7ba2b4f) green on these bytes, so there was no second landing |
| 5be5cb6fc | new `Estimating/OsinUnboundCaseOneRun.lean`. Probe `0913-091600-31828` (base 7dc75e41d) green on these bytes (md5 84aa730b), so there was no second landing |
| 3292f7a20 | the same-cell split: `OsinLemma94CaseOneSameCellStatement` in Face (md5 7cb3ba81); `osinLemma94CaseOne_false_of_walk` and `osinLemma94CaseOneInput_of_walk_of_sameCell` in Run (md5 a869ccef). Probe `0913-093623-11190` green on these bytes, so there was no second landing |
| 48c6cc71e | T: clause (b) of Lemma 9.7 below the cell count threaded into Lemma 9.4 (ten files). Probe `0913-145812-91168` (base 88fc580eb, 16 modules) green on these bytes |

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
3. `Estimating/OsinUnboundCaseOneRun.lean` (5be5cb6fc, restructured in 3292f7a20 and by (A)):
   - `osinLemma94CaseOne_false_of_walk` handles one pair for `ε ≥ 3`, given `hkind`. The
     connectors are respelled nonempty by `WordConnectorPair.exists_nonempty_connectors`.
   - `osinLemma94CaseOneInput_of_walk (hwalk) (hsame) : OsinLemma94CaseOneInput`.
4. The same-cell split (3292f7a20):
   - `OsinLemma94CaseOneSameCellStatement` (in Face) is `OsinLemma94CaseOneInput` with the extra
     hypothesis `P.kind k C.source = P.kind k C.target`.
   - The walk is used only when the two kinds differ.

### LoopCut ruling (A), final (landed f04929ebb)

- `RespectsSections` gains `target ≠ some source` as its first conjunct, so a region from a cell
  to itself is not a candidate.
- ghw-charp2 landed census patches 01-10 as one landing. For this lane's files:
  - patch 09(d)/(e) adds `hloop : target ≠ some source` to `exists_quadrilateral_region_rotate`
    and `false_of_quadrilateral_face`;
  - OC6, this lane's Run patch, rode in (A): `osinLemma94CaseOne_false_of_walk` gains
    `hkind : P.kind k C.source ≠ P.kind k C.target` and derives `hloop` from the side-kind
    conjuncts of the walk, and `osinLemma94CaseOneInput_of_walk` takes `hsame` (patch 10(f)'s
    deletion is overruled).
- So audit-sec3's note that `OsinLemma94CaseOneSameCellStatement` is redundant no longer holds:
  the one-cell pair has no competitor region.

### The one-cell pair

- **A1 premise** (this lane's pick). `P.kind k C.target ≠ P.kind k C.source` is `hkind` in OC6.
- **A2 is false.** A field that forbids two sides on one cell fails whenever an unselected
  `G`-face touches a cell along two short arcs with the arc of another cell between them.
  `Maximal`, `DartMinimal` and least area all allow that.
- **What remains.** The two sides are arcs `p`, `q` of one cell, and both walk portions between
  them have short value. One of the two pockets bounded by a walk portion and a subarc of the
  cell is bounded.
  - Pocket without an R-cell: ko-closed's metric kill (ruling (1)), over
    `OsinLemma94OneCellValue` (ea9016135, 36524dbf0) and `OsinLemma94OneCellMorse` (5063f177b).
  - Pocket with an R-cell: Osin's loop case. jacobson's `nonempty_osinLoopCut_of_pocketRegion`
    gives an `OsinLoopCut`, and `OsinLoopCut.false_of_below` refutes it given the inductive
    assumption, which T supplies.
  - The PocketRegion from the Case 1 walk decomposition is ruled part of jacobson's producer;
    hull-select owns the four-facts producer for non-simple pocket walks.
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
- hull-unbound's verdict: restate `OsinLemma94CaseOneInput` and the walk Prop over gap-free class
  words, plus a named pinched-window item (owner to be ruled). It does not conflict with T.
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
- Inside W1 h94, for this lane's item: `GGT.VanKampen.OsinLemma94CaseOneSameCellStatement`, the
  binder `hsame` of `osinLemma94CaseOneInput_of_walk`, taken as `hsameOne` by ghw-assembly's waist
  (5f031e3a6). jacobson owns its producer. Since T (48c6cc71e) it carries the inductive
  assumption.
- Closed walls: hbridge, hzip, hfold, hT6, and hKO (f65f99f17).

## Census

`metadata/nm-census-rows/theoremc-retire.tsv` has one row, LINE:284, graded
`partial`. Its carriers are the `_of_leastAreaInputs`, `_of_leastAreaKOLeaves`,
`_of_leastAreaZipFold`, `_of_leastAreaFold` and `_of_greendlinger` endpoints (10
declarations). Its note retires the baseline finding "root-imported
TheoremCAssembly has 5 sorries" (census2 U2). The grade stays `partial` while
hgreendlinger is open. There is no Case 1 row yet, since it waits for jacobson's producer.

## Stale references

One item remains: nothing supplies `HullSC.HullRelatorRespellingStatement`. It is still the
binder `hrespell` at `GGT/HullSCLemma44FamilyAssembly.lean:548, 655, 670`,
`GGT/HullSCLemma44QuasiGeodesicBridge.lean:412, 476` and
`GGT/HullSCLemma44RespellingBinders.lean:229`.

## Next

- Sent (15:08), after T landed: hold releases to the five owners, the window line closed in
  wire-queue.txt, and messages to main (T landed, the (A) record correction, hull-unbound's
  verdict, the Count/Covers ruling request), jacobson, ko-closed, ghw-assembly and fff-periodic.
- fff-periodic's Count/Covers binder: a follow-on co-probe on T's binder form, owner by main's
  ruling.
- After jacobson's producer lands: a Case 1 census row (the composition is already on main in
  ghw-assembly's waist).
- Offered to the lead: once GreendlingerLeaf is wired, re-point `SeedFromTheoremC.E` at
  `_of_greendlinger` (Rule 22: probe `SeedRemarkTheoremC` with it).
- One-application flip, this lane: once hgreendlinger closes, the `_of_greendlinger`
  forms become closed Theorem C, and LINE:284 can be regraded.
