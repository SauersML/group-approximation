# ko-closed — the Kotowski–Ollivier input `hKO` from `GHB(7)` (lane ko-closed, clone thm-e, 2026-09-13)

Predecessor: kh-hyperbolic (dead; report `kh-hyperbolic.md`).  Target: `Kazhdan/KotowskiOllivierClosed.lean`,
closed `kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement`.

## STATE (09-13 ~16:10): pick (a) confirmed; cell-free branch of binder 3 offered to jacobson
- hull-unbound landed option (a) as `OsinLemma94PinchedQuadrilateralStatement`, d463383fa (probe 0913-160048-79943
  GREEN, queued).  It is the pick (i) below, so ko-closed confirmed it as final.
  - Scope: a different target cell or a boundary target (`target ≠ some source`).
  - The same-cell pairs stay with binder 3.
  - Its `(side, gap)` pieces carry the gap-reads-1 identities that the OneCellWindow kills take.
- main 15:50: offer jacobson a split of its binder 3 producer (`OsinLemma94CaseOneSameCellStatement`).
  - ko-closed would take the cell-free branch in a new module.
  - jacobson keeps the pocket construction and the R-cell branch (loop cut, `hin` kept under R1).
  - Offer sent 16:00.  Before it went out: no Lean file outside this lane's four modules uses the kills, and
    jacobson's files are unchanged since 13:53.
- Draft `$NM/backup/ko-closed/OsinLemma94SameCellCellFree.draft.lean` (127 lines).  It is not in the tree and not
  probed.
  - `PocketRegion.outer_isRotated_of_decomposition`: `invDarts Q.outer.cycle = invDarts s ++ invDarts A` gives
    `Q.outer.cycle ~r s ++ A`.
  - `false_of_sameCell_cellFree_pocketRegion_X` / `_Y`: the loop-cut spelling, over `osinLemma94CaseOneWalk_sameCell`,
    with `T.darts = q ++ A ++ p`.  They apply the OneCellFace kills.
  - Waiting on jacobson's answers:
    - (a) whether it already wrote this branch;
    - (b) whether the pocket is over `S.diagram` or another O-equivalent copy;
    - (c) decomposition or rotation input.
- Residual Props owned by ko-closed: NONE.

## STATE (09-13 ~15:25): the Morse kill through windows GREEN (0913-150725-78874), queued; pinched-window pick (i)
- hull-unbound's model test (roster l.935), on audit-intro's pinched cell:
  - on class words, every long window contains a pinch junction;
  - a junction window is not a `CyclicArc.reverseDarts`, so literal-arc members refuse it;
  - hull-unbound recommends gap-free class words and one named pinched-window item.
- Kill side, checked against the landed code: `false_of_cellFree_pocket_X_morse` uses the face rotation only through
  values.  A gap-free window `p'` through a pinch vertex skips a loop of `∂Π` that reads 1.  So `p'` reads the inverse of
  the with-gap arc `p~` of `Π`, and `S = q~ M p~` is still a relator subword.  The kill needs no split at the pinch
  vertex and runs at any `ε ≥ ⌈(2κ + c)/λ⌉`.
- `GGT/VanKampen/Estimating/OsinLemma94OneCellWindow.lean` (163 lines):
  - Landed at 07cb99953.
  - GREEN 0913-150725-78874: base 498b0ca80, BUILT, 0 warnings or errors, md5 87cdaa34 equal to origin/main, all five
    `#audit_axioms` pass.
  - Queued for wiring after OsinLemma94OneCellMorse.
  - `Embedded.listVal_dartWord_eq_of_isRotated_windows`: a closed word of value one read as `X q' Y p'`, with
    `val q' = (val q)⁻¹` and `val p' = (val p)⁻¹`, reads `Y` as `q X⁻¹ p`.
  - `listVal_dartWord_eq_of_cellFree_pocket_windows_X` / `_Y`: the value steps.
  - `false_of_cellFree_pocket_windows_X_morse` / `_Y_morse`: the landed binders with `hrot : l ~r X ++ q' ++ Y ++ p'`,
    plus `hq'` and `hp'`.
- The producer still has to supply three things (jacobson, or whoever the lead names for the pinched window):
  - the with-gap arcs, with their two value identities;
  - a cell-free PocketRegion with outer cycle `~r X ++ M`;
  - `T = q~ ++ M ++ p~`.
- audit-sec5's three checks (the constant, the alphabet, the orientation) already hold in the landed code: the Morse
  word is the relator subword `S` at `(λ, c)`, the metrics are joined by `symmetricLabelAlphabet.wordNorm_eq`, and both
  X and Y pockets are covered.
- Pinched-window pick (roster l.1098; team-lead 15:16: hull-unbound owns the item, ko-closed picks): sketch (i), a
  Case 1 member that accepts a window crossing a junction.  Not (ii), the l.850 un-pinch.
  - Why: roster l.786 gates the un-pinch on a Case 1 user that cannot accept a gap window.  The kill side of (i) is on
    main (07cb99953) and reads the windows only through values.  So there is no split at the pinch vertex, and no
    connector from `v` to `T` is needed.  hull-unbound's objection (Morse gives only `ε` plus a constant) does not arise.
  - The item then delivers the class-word form of `osinLemma94CaseOneWalk_sameCell`, for a backwards same-cell pair on
    gap-free class words of cell `j`:
    - windows `p'`, `q'` on the walk `l` of `f` with `l ~r X ++ q' ++ Y ++ p'`;
    - with-gap arcs `p~`, `q~` of `cellDarts j` with `val p' = (val p~)⁻¹` and `val q' = (val q~)⁻¹`;
    - the values of `X` and `Y`, and the norms of the four segments.
  - The producer (jacobson) supplies the pocket: a PocketRegion with outer `~r X ++ M` (or `Y ++ M`) and an arc `T` with
    `T.darts = q~ ++ M ++ p~`.  This pocket contains the bubbles, as Osin's `Γ` does.  If it is cell-free, the kill
    applies.  Otherwise it goes to the loop cut, whose `hin : P.inner.FollowsBoundary` (OsinPocketLoopCut.lean:209) is
    the open point recorded in rulings 15:05.
  - Model: on audit-intro's pinched cell the gaps `abc` read 1, so the identities hold with `p~` the arc through the
    gaps.
- T LANDED 48c6cc71e.  `OsinLemma94CaseOneSameCellStatement` now takes `OsinLemma97Below … Delta.rCellCount` after
  `Delta.LeastArea → 0 < Delta.rCellCount →`.
  - The kills take none of the new binders.
  - Every kill binder is in scope after the statement's intros: `hW`, `hmorse` and `κ` through
    `exists_morse_threshold_of_fourPoint`, `P`, `C`, `hback` and `hkind`.
  - No Lean change on this lane's side.
- team-lead plan: CaseOneInput and the walk Prop are restated over gap-free class words, plus one named pinched-window
  item (hull-unbound).
- Residual Props owned by ko-closed: NONE.

## STATE (09-13 ~14:55): face-level one-cell kills GREEN (0913-145215-56485), queued; OneCellInput withdrawn
- theoremc-retire withdrew `OsinLemma94CaseOneOneCellInput`, so case (a) below is not written against it.  The consumer
  is now jacobson's producer of `OsinLemma94CaseOneSameCellStatement` (roster l.919).  It composes ko-closed's
  cell-free branch (1) with `nonempty_osinLoopCut_of_pocketRegion`, and jacobson routes the PocketRegion.
- `GGT/VanKampen/Estimating/OsinLemma94OneCellFace.lean` (303 lines):
  - Landed at f8d2571ba.
  - GREEN 0913-145215-56485: base f8d2571ba, BUILT, empty error index, md5 76546585 equal to origin/main, all seven
    `#audit_axioms` pass.
  - Queued for wiring.
  - `polygon_segment_value`, `polygon_face_value`, `polygon_face_isRotated`: corner values along a side window, the
    face value 1, and the face rotation read as `X ++ invDarts q ++ Y ++ invDarts p`.
  - `wordNorm_lt_of_start_connector` / `_end_connector` and `lt_wordNorm_of_source_segment` / `_target_segment`: the
    norms from `start_short`, `end_short`, `source_long` and `target_long` over `symmetricLabelAlphabet D`.
  - `osinLemma94CaseOneWalk_sameCell P k C (hback : C.b' < C.b) (hkind : P.kind k C.source = P.kind k C.target)`:
    - one relator cell `j` with `P.kind k C.source = .cell j`;
    - arcs `sourceArc` and `targetArc` of `cellDarts j`, both of positive length;
    - a face rotation `X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts`;
    - the values of `[a, a']`, `[b', b]`, `X` and `Y`.
  - `false_of_cellFree_pocket_face_X_morse` and `_Y_morse` conclude False.  Their inputs:
    - `hW : OsinCCondition`, `0 ≤ λ`, `hmorse`, and `2κ + c ≤ λε`;
    - the polygon and the pair C over `symmetricLabelAlphabet D`;
    - the output of `_sameCell`;
    - a cell-free PocketRegion with outer cycle `~r X ++ M` (or `Y ++ M`);
    - an arc T of cell `j` with `T.darts = targetArc ++ M ++ sourceArc` (or `sourceArc ++ M ++ targetArc`).
- Finding: the landed `OsinLemma94CaseOneWalkStatement` exports no segment values and cannot force
  `target = some source` when the kinds agree.  So the same-cell branch uses `osinLemma94CaseOneWalk_sameCell`, and no
  existing Prop changes.
- Sent to jacobson:
  - the signatures;
  - the threshold: `exists_morse_threshold_of_fourPoint D hhyp λ c hλ`, then `eps0 := max eps1 eps2`.
- jacobson builds Q, M, T and the R-cell branch (Rule 16).  If jacobson spells the pocket differently, the adapter goes in
  my file.  theoremc-retire has been informed.
- Residual Props owned by ko-closed: NONE.

## STATE (09-13 ~14:30): (a) metric kill GREEN (0913-142447-72008) and queued for wiring; value module GREEN
- The lead forwarded three questions to ko-closed (ROSTER 843–850). ko-closed ruled at ~14:10 and sent the ruling to main
  and audit-sec5:
  - (1) audit-sec5's metric kill replaces the `λ⁻¹(ε + c)` respelling. hull-unbound's option (2) draft in
    OsinLemma94Pieces can be cancelled. `osinLemma94AntiparallelMetric` stays as spelled.
  - (2) jacobson's `nonempty_osinLoopCut_of_pocketRegion` (OsinPocketLoopCut, GREEN 0913-135346-38278) produces (b).
    audit-sec5 writes no second LoopCut producer.
  - ko-closed writes (1), not audit-sec5. audit-sec5 was asked for any draft statement, so that its spelling is used
    rather than duplicated.
- The kill:
  - `WordConnectorPair` (UnboundWordConnectors:43-46) has `source_long` and `target_long`: both sides span a word
    distance greater than ε.
  - The value lemmas below make the cell arc `S = A M B` read a connector, so `|val S| < ε`.
  - A Morse radius κ for `(λ, c)` exists before ε₀. It comes from `isHyperbolicSpace_cayley_of_fourPoint` and
    `exists_word_replacement_morse`. δ, λ and c are bound before `eps0` in `OsinLemma94CaseOneInput` (PlanarPieces:397),
    so no statement changes.
  - Morse gives `d(x0,x1) + d(x1,x3) ≤ 2κ + d(x0,x3)`. The subpath bound gives `λ|B| − c ≤ d(x1,x3)`.
  - So `λε − c < 2κ`, which fails once `ε ≥ ⌈(2κ + c)/λ⌉`. No DartMinimal, Maximal or least area is used.
- Correction to the ~13:25 STATE below: Shape 1 checked only the whole-arc bound. With the subpath bound and a Morse
  radius it forces `ε < (2κ + c)/λ`. So it is not a counterexample at the printed threshold.
- (b) belongs to jacobson (Rule 16).
- `GGT/VanKampen/Estimating/OsinLemma94OneCellValue.lean`:
  - GREEN 0913-135819-58619 (base 36524dbf0, BUILT, empty error index, all nine `#audit_axioms` pass).
  - Landed at ea9016135. The fix `List.nil_rotate` → `List.rotate_nil` landed at 36524dbf0.
  - Queued for wiring.
  - Its lemmas take ordinary hypotheses:
  - `Embedded.listVal_dartWord_eq_inv_of_isRotated`: a closed word of value one, rotated to `s ++ t`, reads `t` as
    `s⁻¹`.
  - `PocketRegion.listVal_outer_eq_one` and `listVal_eq_inv_of_outer_isRotated`: the outer cycle of a cell-free pocket
    reads 1, so `M'` reads `X⁻¹`.
  - `Embedded.listVal_dartWord_eq_of_isRotated_invDarts`: the face gives `Y = q X⁻¹ p`.
  - `Embedded.CyclicArc.exists_darts_eq_of_rotate_eq`: a prefix of a rotated carrier is an arc.
  - `Embedded.CyclicArc.lambda_mul_length_sub_le_wordNorm` and `false_of_wordNorm_add_lt`: a cell arc of length `L`
    reads an element of word norm at least `λL − c`.
  - `false_of_cellFree_pocket_X` and `false_of_cellFree_pocket_Y`: the value argument in its two cases (pocket across
    X, or across Y).
- `GGT/VanKampen/Estimating/OsinLemma94OneCellMorse.lean` (237 lines):
  - Landed at 5063f177b.
  - GREEN 0913-142447-72008: base 5063f177b, BUILT, empty error index, all seven `#audit_axioms` pass.
  - Queued for wiring after OsinLemma94OneCellValue, which it imports.
  - `IsLambdaCQuasiGeodesicWord.vertex_detour_le_morse`: under `UnboundEstimate.IsWordMorseRadius D λ c κ`, vertex
    `i` of a quasi-geodesic word has `|x_i| + d(x_i, val w) ≤ 2κ + |val w|`.
  - `IsLambdaCQuasiGeodesicWord.lambda_eps_lt_of_hairpin`: for a quasi-geodesic word `A ++ M ++ B` with `0 ≤ λ`,
    `|val (A++M++B)| < ε`, `ε < |val A|` and `ε < |val B|`, we get `λε − c < 2κ`.
  - `exists_morse_threshold_of_fourPoint D hhyper λ c (0 < λ)`: `∃ κ, IsWordMorseRadius D λ c κ ∧ ∃ eps0, ∀ ε ≥ eps0,
    2κ + c ≤ λε`.
  - `listVal_dartWord_eq_of_cellFree_pocket_X/_Y`: the value step as named lemmas. The value module keeps its queued
    bytes.
  - `false_of_cellFree_pocket_X_morse` and `_Y_morse`:
    - binders as `false_of_cellFree_pocket_X/_Y`, plus `hmorse` and `hthreshold : 2κ + c ≤ λε`;
    - instead of `hlong`: `hY : |val Y| < ε` (`hX` for the Y case), `hp : ε < |val p|`, `hq : ε < |val q|`;
    - conclusion False.
- Not written: case (a) of theoremc-retire's `OsinLemma94CaseOneOneCellInput`, which is not on main. The consumer then
  supplies:
  - the face value 1, from `inner_face` with f a G-face;
  - the walk rotation;
  - a PocketRegion whose outer cycle is `X ++ M'` (or `Y ++ M`);
  - the arc `q M' p` as a rotation prefix of `cellDarts j`;
  - `hp` and `hq` from `source_long` and `target_long`. The face reads `invDarts p`, so this needs `wordNorm_inv`, and
    `symmetricLabelAlphabet.carrier_eq` because the pair lives over `symmetricLabelAlphabet D` while `OsinCCondition`
    is over D;
  - `hY` or `hX` from `startConnector` or `endConnector`, which have length `< ε`, via `wordNorm_listVal_le_length`;
  - κ and eps0 from `exists_morse_threshold_of_fourPoint`, taken into the max with the other thresholds.
- Open question to jacobson: who produces the PocketRegion from the Case 1 walk decomposition.
- Residual Props owned by ko-closed: NONE.

## STATE (09-13 ~13:25): one-cell Case 1 (team-lead's assignment), model test FAILED at (a); no Lean written
The assignment has two parts, both for theoremc-retire's `OsinLemma94CaseOneOneCellInput`:
- (a) a pocket with no R-cell ⇒ False;
- (b) a pocket with an R-cell ⇒ `Nonempty (OsinLoopCut …)`.
That statement is not landed, and its text has not arrived.
- Shape 1 is a paper picture, not a formal refutation; there is no global model yet.
  - Face f runs along cell Π on consecutive sides A (source) and B (target), both `.cell j`.  At their common vertex,
    Π's boundary makes a spur, so the relator contains `x x⁻¹`.  This is legal once `c ≥ 2λ`.
  - Then `X = []` and the pocket has no face.  P.Maximal holds (`facePerm (alpha e') ≠ alpha e`).  f has no spur, so
    NoLoops, GFacesApart and DartMinimal give nothing.
  - The hairpin `B⁻¹ x x⁻¹ A⁻¹` has as its value the start connector (`< ε`).  The `(λ, c)` bound allows this at every
    large `ε` when `λ < 1/2`.
  - Consequences:
    - The planar pocket lemma "arcs of the cell plus spurs, a spur at every junction" is false, so it is not named.
    - (a) does not follow from CaseOneInput's hypotheses.
    - No loop cut exists.
- Shape 2 is a lake inside a loop of `∂Π`, holding one G-face (`x y x⁻¹ y⁻¹` with x, y commuting).  The vertex-split merge
  into f keeps the dart count.  So shape 2 survives DartMinimal and dies under (darts, faces) minimality.
- The value argument proves (a) with no spur, Maximal or DartMinimal input:
  - a cell-free pocket gives `|B⁻¹M'A⁻¹|_G < ε`;
  - that is a contradiction once `d(a,a') + d(b',b) ≥ λ⁻¹(ε + c)`, or when `λ > 1/2` and `ε₀ > c/(2λ−1)`.
- (b) needs the X-pocket as a PocketRegion plus a collar.  `side_short` bounds the section length, and X can be long.
- The model test and the options went to main and theoremc-retire:
  - (1) count one-cell pairs separately (A1, roster 590);
  - (2) a longer one-cell threshold from the metric lemma.
  Waiting for the ruling.
- Residual Props owned by ko-closed: NONE.

## STATE (09-13 ~10:50): `OsinLemma94CellArcsInput` PROVED (hull-unbound's realization split, 1130c8dbc)
`theorem GroupApproximation.GGT.VanKampen.osinLemma94CellArcsInput_holds : OsinLemma94CellArcsInput.{u, w, v}` is in
`GGT/VanKampen/Estimating/OsinLemma94CellArcs.lean` (51 lines), the team-lead's assignment.
- The statement is unchanged (`Estimating/OsinLemma94PolygonRealization.lean:121`, md5 aca16686).  The Prop is true as
  spelled, and the hypothesis `0 ≤ c` is not used.
- The proof:
  1. An arc of a relator cell read from across spells `revInv` of a prefix of a cyclic shift of the relator.  So the
     existing `CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts` (`OsinPocketCellArcs.lean`) makes it
     `(λ, c)`-quasi-geodesic over `D`.  `invDarts arc.darts = arc.reverseDarts` holds by `rfl`.
  2. `isLambdaCQuasiGeodesicWord_symmetricLabelAlphabet` (new) moves the word to the symmetric label alphabet
     (`symmetricLabelAlphabet.admissible`, `carrier_eq`) and raises `c` to `c + 2` (`linarith`).
- LANDED 5e5a98049 (unverified, then probed).  Probe 0913-104724-79090 (base 5e5a98049) BUILT it GREEN, with bytes md5
  cb741b4c equal to origin/main.
- `#audit_axioms` on both theorems throws outside propext, Classical.choice and Quot.sound, so the green build certifies
  them.  Wire-queued at 5e5a98049.
- No census row: no line of the tex cites Lemma 9.4.  The consumer is `osinLemma94PolygonRealizationInput_of_pieces`
  (hull-unbound).
- Residual Props owned by ko-closed: NONE.

## STATE (09-13 ~10:00): `OsinLemma94CaseOneWalkStatement` PROVED (theoremc-retire's walk sub-piece)
`theorem GroupApproximation.GGT.VanKampen.osinLemma94CaseOneWalk : OsinLemma94CaseOneWalkStatement.{u, w, v}` is in
`GGT/VanKampen/Estimating/OsinLemma94CaseOneWalkHolds.lean`.  The list and arc facts are in
`OsinLemma94CaseOneWalkLists.lean`.
- The statement is unchanged: theoremc-retire's fd6ce3c09, md5 6038689296f15b2d6c53c5ea0fe70625.  Every conjunct is true
  as stated, so no counter-shape was sent.
- No binder, sorry or axiom, with `#audit_axioms` in both modules.
- LANDED:
  - eb9010962: both modules, unverified;
  - 8f0f73966: the linter fix.
- Probe 0913-094857-38535 built Lists green and stopped Holds at one linter error, `exact hkt` after `rfl`.
- Probe 0913-095509-55850 (base c99e3bec1) built Holds GREEN.
  - `osinLemma94CaseOneWalk` depends on propext, Classical.choice and Quot.sound.
  - Wire-queued: Lists at eb9010962, Holds at 8f0f73966.
- A grep for `9\.4` in the tex finds nothing, so this piece has no census row of its own.  Its consumer is theoremc-retire's
  `OsinLemma94CaseOneInput`.
- The proof:
  1. The walk of polygon `k`, rotated to `base k`, is the concatenation of the sides.  So `[a, a']` and `[b', b]` are windows
     at the block starts (`rangeFlatMap_split`, `rangeFlatMap_drop_take`).
  2. Rotating to `a'` reads `X ++ T ++ Y ++ P` (`rotate_four_inside` or `rotate_four_wrap`, depending on which side comes
     first).
  3. Corners are prefix values and the whole walk has value 1 (`polygon_vertex_eq`, `walk_four_windows`), which gives the
     values of `X` and `Y`.
  4. `P` and `T` are sub-arcs of the arcs from `cell_arc` and `boundary_arc` (`cyclicArc_exists_sub`,
     `cyclicArc_exists_sub_reverse`).  An `∂Δ` arc inside section `j` ends by `cut (j+1) ≤ |∂Δ|`, so its sub-arc does
     not wrap and stays inside the section.
- Residual Props owned by ko-closed: NONE.

## STATE (09-13 ~07:20): hKO and SharpExistence CLOSED; flip item withdrawn (hull-bridge)
`theorem GroupApproximation.KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed :
Manuscript.NonMF.TheoremC.KotowskiOllivierStatement :=
kotowskiOllivier_of_pinched (Systolic.mirrorFoldPinched CCKW.cosetComplex)`, and
`theorem GroupApproximation.Hyperbolic.sharpExistence_closed : SharpExistence := kotowskiOllivier_closed`.
- Neither endpoint has a binder.  `#audit_closed_axioms` passes on both with propext, Classical.choice and Quot.sound.
- `sharpExistence_closed` LANDED b0ab67b4a after probe 0913-065114-20727 (base c48f20f41) went green.  Wire-queued at
  b0ab67b4a (the module is root-reachable).  `kotowskiOllivier_closed` LANDED f65f99f17.
- Every leaf is closed:
  - hzip is `CCKW.zipSpur_cosetComplex` (`GGT/SystolicDiscZip.lean`, 8389a0e6c, kh-torsion);
  - Distinct is `Systolic.mirrorFoldDistinct` (81b06b43e, ko-closed);
  - Pinched is `Systolic.mirrorFoldPinched` (`GGT/SystolicDiscMirrorFold.lean`, 426813b24, fff-periodic).

  hT6 is not needed: `sharpExistence_ghb7_of_zipFoldHyp`.
- Residual Props owned by ko-closed: NONE.

## ASSIGNMENT (lead, 09-13 ~06:50)
1. `Hyperbolic.SharpExistence` with no binder: DONE, `Hyperbolic.sharpExistence_closed` (b0ab67b4a).
2. WITHDRAWN by the lead (~07:15).  hull-bridge owns the flips for nm-endpoints' five endpoint modules: it has unlanded
   drafts `TorsionFreeGreendlingerForms.lean` and `TorsionFreeGreendlingerSentences.lean`, and the roster's
   "Reassignments 09-13 ~06:30" gives it those modules.  ko-closed wrote nothing for them.  Before the withdrawal,
   ko-closed found and sent nm-endpoints and census the following (the mapping is in this report at 62e77b1cf):
   - fff-periodic's `TorsionFreeGreendlingerLeaf` (1edf0f7b4) already has forms that take `hgreendlinger` alone;
   - the 18 old declarations are named only in sec5-sentences' rows LINE:284, 291, 1636, 1650 and 1718;
   - `TorsionFreeGreendlingerLeaf` is imported by nothing.  I reported it as missing from the wire queue, but that was
     wrong: my grep was cut off at five matches.  It is queued at line 501 (fff-periodic, 06:45).
3. Row 8097c371f35d is nm-endpoints' file (`metadata/nm-census-rows/nm-endpoints.tsv`); do not land it.  Its carriers are
   the `TorsionFreeFourLeaves` forms.  Baseline lines 369-370 (`kotowskiOllivier_of_leaves`, open-predicate and
   buried-conditional, census merge 63f147d7b) came from ko-closed's old LINE:1675 row, which dropped that carrier at
   2d25ebab5.  Row LINE:1675 now names `kotowskiOllivier_closed` and `Hyperbolic.sharpExistence_closed`, and drops
   `kotowskiOllivier_of_pinched`, which has a binder.  I sent both `_closed` names to nm-endpoints, who swaps and
   re-grades their own row, and asked census to retire the two lines at its next merge.

## LANDED (all GREEN, all wire-queued)
| module | SHA | probe |
|---|---|---|
| `Kazhdan/KotowskiOllivierClosed` (`kotowskiOllivier_of_leaves`) | c5a8ae8fb | 0913-011617-71747 |
| `GGT/SystolicDiscMirrorFoldCases` (Distinct/Pinched Props, `mirrorFoldStatement_of_cases`, `faceOf_alpha_ne_of_inner`) | 0fb6f2305 | green |
| `GGT/SystolicDiscMirrorFoldSteps` (`digonBack`, `CycleDisc.exists_of_embed`) | 79b8c51c8 | green |
| `GGT/SystolicDiscMirrorFoldQuad` (`MirrorQuad`, three moves, `planar3`, `faceCount_add_two`) | b110363ae | 0913-041349-71786 |
| `GGT/SystolicDiscMirrorFoldEmbed` (`tau`, `tau_facePerm`, `tau_injective`, `tau_cases`, `exists_tau_eq_of_ne`) | 781dcb8bf | 0913-042826-7309 |
| `GGT/SystolicDiscMirrorFoldDistinct` (`mirrorFoldDistinct`) | 81b06b43e | 0913-044647-45237 |
| `Kazhdan/KotowskiOllivierClosed` (`kotowskiOllivier_of_pinched`, the one-leaf reduction) | cf1675f3b | 0913-045023-55941 |
| `Kazhdan/KotowskiOllivierClosed` (docstring: the `hKO` binders after 2c3c8cb40, reported by sec2-sentences) | 4be3a3a5c | 0913-052526-4611 |
| `Kazhdan/KotowskiOllivierClosed` (`kotowskiOllivier_closed`; imports `GGT/SystolicDiscMirrorFold`) | f65f99f17 | 0913-055250-45566 |
| `Kazhdan/KotowskiOllivierClosed` (`Hyperbolic.sharpExistence_closed`) | b0ab67b4a | 0913-065114-20727 |

Census row LINE:1675 (`kotowskiOllivier_closed`, `Hyperbolic.sharpExistence_closed`, partial).  It closes the `hKO`
input only, and the rest of the sentence belongs to other rows.

`theorem mirrorFoldDistinct (X : TriangleComplex V) : MirrorFoldDistinctStatement X`.  `#print axioms` gives propext,
Classical.choice and Quot.sound.  dgo-geometric independently audited the Prop as true.

## hfold SPLIT (Option A, agreed with fff-periodic)
Setup: `d : a→b` in the inner face `[d, d1, d2]`, `alpha d` in `[alpha d, e1, e2]`, and the third corners carry one label.
- DISTINCT (ko-closed, CLOSED), in three moves:
  1. Delete the edge of `d`, which leaves a square.
  2. Fold `d2` onto `alpha e1` (`FoldMap.IsFoldable`: the two ends differ).
  3. Delete the digon edge `e2''`.

  The final map embeds in the disc by `tau` along face rotation, reads labels compatibly and covers the exterior
  cycle.  So it is a cycle disc with the same boundary and two faces fewer.
- PINCHED (fff-periodic, CLOSED): edge deletion, vertex split, restriction to the outer component, digon deletion
  (`FoldStage.exists_disc_of_pinch`, 08ae1c587).
- The final composition `Systolic.mirrorFold (X) : MirrorFoldStatement X` landed in fff-periodic's
  `GGT/SystolicDiscMirrorFold.lean` (426813b24).  My draft of the same composition is dropped, and nothing was landed at that path.

## ORPHANS
`Kazhdan/KotowskiOllivierLeaves.lean` → ko-closed.  VERDICT (accepted by the lead): leave it; no deletion.  Nothing on main
imports it.

## COORDINATION
- theoremc-retire (~06:00):
  - flip `hKO := KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed` in the `_of_leastAreaInputs` forms and
    `SeedFromTheoremC`, once `Kazhdan.KotowskiOllivierClosed` is wired;
  - also, `hfold := Systolic.mirrorFold CCKW.cosetComplex` for the `_of_leastAreaZipFold` forms.
- nm-endpoints (~06:00): the rows that waited on `hpinch` now wait on wall 1 only.
  - ~07:10: I proposed a split for item 2.
  - ~07:15: they replied that no split is needed and hull-bridge owns the flips.  Row 8097c371f35d is in their tsv,
    and they swap its carrier themselves.  I sent them `kotowskiOllivier_closed` and `Hyperbolic.sharpExistence_closed`.
- census (~07:10): asked to retire baseline lines 369-370.  (~07:15): told that no five-module mapping will come.
- main (~07:10): milestone report, plus the unwired `TorsionFreeGreendlingerLeaf`.
- kh-cckw: the every-X HC6 is `Systolic.mirrorFold`.  This corrects my earlier name `mirrorFoldStatement`.
- sec2-sentences: docstring fixed (4be3a3a5c).

## NEXT (lead, 09-13 ~07:25; restated after the ~08:30 restart): help theoremc-retire with `OsinLemma94CaseOneInput`
The Prop is in hull-unbound's `GGT/VanKampen/Estimating/OsinLemma94PlanarPieces.lean` (80790fad1).  theoremc-retire
landed the face-walk piece `OsinLemma94CaseOneWalkStatement` (`Estimating/OsinLemma94CaseOneWalk.lean`, 8a36ad06c).
theoremc-retire assigned ko-closed the walk piece.  It is proved, as recorded in STATE above.  theoremc-retire owns pieces
(a)-(d) below.

Findings sent to theoremc-retire and main.  Two gaps separate CaseOneWalk from
`RealizedSectionFamily.false_of_quadrilateral_region`:
- (B1) `NoInternalFaceDart` for `P.face k` is false when polygon `k` has a cutting side, because `cutting_internal` puts
  both sides of the path in face `k`.  So `FaceSetBoundary.ofSingleton`, and with it the singleton `InnerGRegion`, is
  unavailable.  But `GFaceWordInsertion.exists_quadrilateral_region` uses `hno` only in `hold_face`
  (`GFaceQuadrilateralRegion.lean:255-262`), applied at :280 to darts of the source arc `P` and at :290 to darts of the
  target arc `T`.  For those darts `faceOf (alpha z) ≠ f` follows from `hcells` and `hf`.
- (B2) CaseOneWalk gives `darts.rotate r`, while the surgery needs `r = 0`.  `faceBoundary` is a `DiscDiagram` field
  (`DiscDiagram.lean:111`), but re-basing it does not carry `S` by `rfl`.

Proposed pieces:
- (a) a rotated, `hno`-free `exists_quadrilateral_region`;
- (b) `false_of_quadrilateral_face` on `S.diagram` directly;
- (c) connector glue: `s1 := endConnector`, `s2 := startConnector`, an empty connector padded to `[l, inv l]` with `l`
  a label on `P`, and `eps0 ≥ 2`;
- (d) the assembly `OsinLemma94CaseOneInput`.

nm-endpoints swaps the carrier on its row 8097c371f35d, and census retires baseline lines 369-370 at its next merge.
