# w1-binder-7 lane report

A lane of session nonsofic-existence-49, wave 2: an independent second start on binder 7 of the post-(A) W1 waist,
`PocketPinchLabelledStatement` (`Estimating/OsinPocketPieces.lean:272`). The owners are hull-respell, kh-cckw,
go-lemma42, ghw-assembly and audit-sec3. This lane never edits their files.

## 2026-09-13 ~17:05: state found

- The binder is FALSE as stated. dgo-geometric's `OsinPocketWrapRose.pocketPinchWrapRefutation` (6dfa779fe, 87358b0ad; probe
  0913-163031-39703 GREEN) proves `¬ PocketPinchLabelledStatement.{0,0,0}` and `¬ PocketPinchStepStatement.{0,0,0}`.
  The witness is a three-petal rose at `ε = 0` whose relator words and boundary word have one letter.
- Every assembly that consumes the binder therefore consumes a false Prop: `sectionPocketCutInput_of_pieces`,
  `osinSectionPocketCutSection_of_residuals`, `OsinDescentResiduals` and `OsinGreendlingerOpenResiduals`.
- dgo-geometric named two untested repairs, a `0 < ε` binder and long relators, and left the choice to the lead. There is no
  roster ruling since 16:17, and ghw-assembly has parked the wrap case.

## CLAIM

- CLAIM binder-7 repair interface (`0 < ε`): `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketPinchPositive.lean`
  (new module).
  - `PocketPinchLabelledPosStatement` and `PocketPinchStepPosStatement` state the binder and the step with `0 < eps` added.
  - The implications from the unrepaired Props, and the step induction at `0 < eps`.
  - `sectionPocketCutInput_of_residualsPos` and `osinSectionPocketCutSection_of_residualsPos` (threshold `max eps0 1`),
    so the section-level consumer needs only the repaired binder.
- CLAIM evidence that the refutation does not transfer: `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketWrapRoseRescue.lean`
  (new module). On dgo-geometric's `wrapDiagram`, for every `ε ≥ 1` the face set `{R}` with `s_1 = [5]` and empty arcs is a
  simple pocket face set in positions `0..1`.

## LANDED 1b4736bcb (probe 0913-170902-87292 GREEN, BUILT and COMPILED for both modules)

Both modules are new and unwired, and are queued for wiring. They certify no printed sentence, so they add no census row.

- `Estimating/OsinPocketPinchPositive`:
  - `PocketPinchLabelledPosStatement` and `PocketPinchStepPosStatement`: the binder and the step with `0 < eps`.
  - `pocketPinchLabelledPosStatement_of_labelled` and `pocketPinchStepPosStatement_of_step`: the old Props give the repaired ones.
  - `pocketPinchLabelledPosStatement_of_stepPos`: hull-respell's induction at `0 < eps`.
  - `sectionPocketCutInput_of_residualsPos` (takes `heps : 0 < eps`).
  - `osinSectionPocketCutSection_of_residualsPos hfaces hpinch hgeodesic : OsinSectionPocketCutSectionStatement`, at
    threshold `max eps0 1`.
- `Estimating/OsinPocketWrapRoseRescue`:
  - `rescueK eps heps` and `rescueK_simple`;
  - `wrapRoseRescue : WrapRoseRescue`, which passes `#audit_closed_axioms`.

## LANDED 4db9c6729 (probe 0913-171243-3240 GREEN, BUILT and COMPILED)

- `Estimating/OsinDescentResidualsPos`: `osinDescentSection_of_residualsPos` and
  `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsPos`, the two assemblies of `OsinDescentResiduals` with the repaired
  pinch. The module is unwired and queued for wiring.

## 2026-09-13 ~17:35: after the lead restart, the wrap residual

- CLAIM, the full-arc characterization of the wrap case: `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketFullArc.lean`,
  a new module.
  - `PocketFaceSet.not_simple_of_full_sourceArc`: in ANY diagram, a pocket face set whose source arc is the whole cell cycle is
    not simple, unless its cycle is that reversed arc alone.
  - `PocketFaceSet.not_simple_of_full_targetArc`: likewise when the target arc is the whole exterior cycle, unless the cycle is
    that arc alone.
  - Consequence: the wrap case is exactly a full arc with a nonempty remainder. Doublings and splits transport arcs and sides
    and keep a full arc full, so no transport-based step closes it. The step has to re-decompose the walk.
- CLAIM, the trims at `0 < eps`, in a second new module after that one: move one dart of an arc into a side with room. The
  cycle is unchanged, so walk order and repeated visits are unchanged, and the data stop being wrap data.
- Agreed with ms-intro-4, which takes "first-turn order survives the edge doublings" in
  `Estimating/OsinPocketEdgeDoublingFirstTurns.lean`.
- Agreed with ms-inverses-2:
  - (A) first-turn model tests on the rose, `Estimating/OsinPocketWrapRoseFirstTurn.lean`;
  - T2, first-turn order across the exterior spur thickening (`OsinPocketOuterSpur`). T1 and T1′ belong to ms-intro-4.
- Agreed with ms-cite-1: it runs the counterexample search for `PocketPinchLabelledPosStatement` at `ε ≥ 1`
  (`Estimating/OsinPocketPinchPosModels.lean`). This lane keeps the positive route.
- **LANDED 514e47490** `Estimating/OsinPocketFullArc` (probe 0913-180300-88794: BUILT and COMPILED; the co-probe was red
  only on ArcTrim). The module is unwired and queued for wiring.
  - `PocketFaceSet.not_simple_of_full_sourceArc K hfull hrest : ¬ K.Simple`, where hfull is
    `K.sourceArc.length = (cellDarts X K.source).length` and hrest is
    `K.firstSide ++ K.secondSide ++ K.targetArc.darts ≠ []`.
  - `PocketFaceSet.not_simple_of_full_targetArc K hfull hrest`, where hfull is `K.targetArc.length = (outerDarts X).length`
    and hrest is `K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ≠ []`.
  - Helpers: `PocketFullArc.cyclicRel_rotate`, `darts_eq_rotate_of_full`, `outerDarts_chain`, `outerDarts_cyclic`,
    `closes_mem`, `mem_getLast?_append_singleton`, `PocketFaceSet.invDarts_eq_tail_append`.
  - Calibration: `PocketFullArc.wrapK_not_simple` passes `#audit_closed_axioms`.
  - The first probe (0913-175113-42314) was red on deprecated option lemmas and two simp goals, since fixed.
- **LANDED d5821cd77** `Estimating/OsinPocketArcTrim` (probe 0913-180605-99266 GREEN, BUILT and COMPILED). The module is
  unwired and queued for wiring.
  - `CyclicArc.dropLastArc`, `CyclicArc.tailArc` and their `_darts` lemmas.
  - `PocketFaceSet.trimSourceLast K hlabel hne hroom`, with `hroom : K.firstSide.length < eps`.
  - `PocketFaceSet.trimTargetHead K hlabel hne hs hroom`, with `hs : K.targetArc.start.1 < (outerDarts X).length` and
    `hroom : K.secondSide.length < eps`.
  - `closedWalk_`, `repeatedVisits_` and `simple_..._iff` for both trims: the cycle is unchanged.
  - `trimSourceLast_sourceArc_lt` and `trimTargetHead_targetArc_lt`: the trimmed arc is not full.
  - The first co-probe (0913-180300-88794) was red on one decomposition goal, since fixed.
- **Re-decomposing inside `X` is not a proof route (paper, 2026-09-13 ~18:20).**
  - Instance: the long rose over `F(a,b)` at `ε = 1`, `N = 3`.
    - `Π = aᴺ` and `R = bᴺ`, each with `N` darts. The exterior is a single dart labelled `c = aᴺbᴺ`.
    - `κ` is a G-face whose walk is `inv(∂Π)`, the `c`-loop, `inv(∂R)`, all at one vertex `v`.
    - `K = {κ, R}`: source `Π`, `t₁ = ∂Π`, `t₂ = [c]`, empty sides.
  - No face set of `X` is a simple pocket face set:
    - `{Π}` or `{R}`: both arcs empty, and the sides would need `N > 2ε` darts;
    - `{κ, R}` or `{κ, Π}`: the boundary is a closed cycle through `v` plus the `c`-loop at `v`, so every walk order visits
      `v` twice;
    - `{κ, Π, R}` has no source, and `{κ}` has no kept cell.
  - Both lobes of `K` fail:
    - the pocket side of `inv(∂Π)` contains the exterior;
    - the pocket side of the `c`-loop holds every relator cell.
  - A rebuilt O-equivalent copy does rescue it: `F′ ∋ R`, bounded by `[c]`, `N − 1` darts of `Π`, and `[a]`, with the sides
    exactly those produced by `trimSourceLast` and `trimTargetHead`.
  - So the innermost-circuit rescue of ms-cite-1's record 5f21c733e does not prove the Pos binder, and the step has to build
    copies: trim, double the trimmed side dart, split.
- **LANDED b2c347f69 `Estimating/OsinPocketTrimDouble`** (probe 0913-183017-52812 GREEN, BUILT and COMPILED; unwired, queued
  for wiring), the first stage of the wrap-case step:
  - `PocketFaceSet.exists_trimDouble K hlabel hne hroom hlen hK`: first `trimSourceLast`, then hull-respell's
    `faceEdgeDoubling` at the source face on the trimmed dart. After the trim that dart is off the source arc, which supplies
    `hsrc`.
  - The output is an O-equivalent copy with letter labels and a pocket face set in walk order in the same positions: same
    repeated visits, a source arc one dart shorter, and a first-side dart whose across-face is the new digon. The digon is a
    G-face that is not the exterior, not a relator face, and not in the face set.
  - Rotation at the junction vertex `p` after the doubling (paper, from `EdgeInsertion.toCombMap`): `embed x → none →
    embed(head t₁)`, where `x = α(last t₁)`. The corner after `embed x` is the digon, so `embed x` is a legal split dart
    `I.x`.
  - Still open: the second split dart. It needs a G-corner outside the face set in the other gap at `p`, for the wrap shape
    with `t₂` full (the exterior corner, through kh-cckw's outer spur thickening), and the StretchAvoids chain.
- **2026-09-13 ~19:05: the Pos binder is refuted at `ε = 1` (paper; ms-cite-1 is building the Lean model).**
  - The model: F(a,b,d,e,x,y) with the letter `c = x·aab·x⁻¹·y·dde·y⁻¹`, cells `aab` and `dde`, boundary `[c]`.
  - The hypothesis pocket has a full `t₁`, a full `t₂`, and sides `[x]` and `[x⁻¹]` at `ε`.
  - In any copy, a simple `K′` has `t₂ = []` and a proper `t₁` (by FullArc). Van Kampen then gives `α·p⁻¹·β` conjugate to
    `r^{±1}` with sides of norm ≤ 1, and exponent sums together with kill maps exclude every case. I checked this and found
    no rescue.
  - Correction: longer relators alone do not generalize the model to `ε ≥ 2`. Sides `[c, x]` and `[u⁻¹, x⁻¹]` rescue it
    algebraically. The conjugator has to scale to `x^ε` (paper only).
- **Binder 6 check (fe02830d0, `OsinPocketFaceSetOnCopy`).**
  - Delivered: `SectionPocketFaceSetInput` carries only an O-equivalent copy, letter labels, and a pocket face set in walk order.
    Internally, `PocketWalk` has `t₁ = x.arc ++ Gap ++ y.arc`, sides from region sides (`≤ ε` only), and nonempty arcs.
  - Room is not supplied.
  - A proper `t₁` is not supplied and does not follow from `a ≠ b`, because both region arcs lie inside `t₁`.
  - A proper `t₂` is not supplied.
  - Missing clause sent to main, to be done additively:
    - `SectionPocketFaceSetProperInput`, whose conclusion adds `K.sourceArc.length < (cellDarts X′ K.source).length`;
    - its producer residual `SectionPocketProperGapStatement`: `x.arc.length + Gap.length + y.arc.length` is below the cell
      length.
- **LANDED d07c38405 `Estimating/OsinPocketPinchSection`** (probe 0913-192709-1953 GREEN; unwired, queued for wiring). This is the
  spelling main ruled and agreed with ms-cite-1. ms-cite-1 had proposed the section-family context instead; it was declined
  because it does not tie `K` to the regions.
  - `SectionPocketFaceSetProperInput` (with `.toInput`) and `OsinSectionPocketFaceSetProperSectionStatement`: binder 6 with
    `K.sourceArc.length < (cellDarts X′ K.source).length`.
  - `PocketPinchLabelledSectionStatement`.
    - Premises: the OsinCCondition prefix, `X.LeastArea`, letter labels, `K.ClosedWalk`, and a proper source arc.
    - Conclusion: `∃ X′ K′`, an O-equivalence and `K′.Simple`.
    - No `t₂` premise, since the producer cannot supply one; that is the open truth risk.
    - The ε = 1 model is excluded, since its `t₁` is full.
  - `pocketPinchLabelledSectionStatement_of_pos`: the Section form follows from the Pos form, at `ε₀ = ρ₀ = 1`.
  - `sectionPocketCutInput_of_residualsSection` and `osinSectionPocketCutSection_of_residualsSection` (thresholds `max ε₀`,
    `max ρ₀`).
  - `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopyProper`: the V2Copy route with binders 6 and 7 in these forms.
    The name was sent to ct-bilateral-cell for its v3 waist.
  - Open:
    - w1-binder-6's `SectionPocketProperGapStatement`;
    - model tests of the Section spelling: non-full `t₁` with sides at `ε`, and long relators under OsinCCondition;
    - `CellPocketPinchPosStatement` (binder 5) likely needs the same respelling.
- **LANDED b4856b5c3 `Estimating/OsinPocketPinchStepSection`** (probe 0913-195943-3764 GREEN, BUILT and COMPILED; unwired, queued
  for wiring).
  - `PocketPinchStepSectionStatement`: one step of the section pinch. Under the Section premises, a pinched pocket in walk order
    with a proper source arc has an O-equivalent copy with letter labels, walk order, a proper source arc and fewer repeated
    visits.
  - `pocketPinchLabelledSectionStatement_of_stepSection`: the step gives `PocketPinchLabelledSectionStatement` by strong
    induction. Least area passes to each copy through `OEquivalentDiscDiagram.leastArea`.
  - `PocketFaceSet.pinchSplit_source_proper` and `pinchSplitInside_source_proper`: a vertex split keeps a proper source arc.
  - `PocketFaceSet.exists_pinchStepSection_of_avoids` and `exists_pinchStepSection_of_inside`: both splits on main package
    into the step, given their turn and stretch hypotheses.
  - The first probe (0913-194551-47288) was red: lengths across the split were rewritten at mismatched dart types. It was
    fixed in term mode.
  - After the ~20:03 outage: the green probe finished at 20:01 on bytes identical to attic 9af998f39, and no import had
    changed since its base 74696702a, so it landed without a re-probe.
- **In flight: `Estimating/OsinPocketPinchFirstTurnSection`** (attic 76331da9e, probing), the second split dart under the Section
  premises.
  - It uses ms-intro-4's landed `OsinPocketPinchFirstTurn` (5c9707cfe). For a turn `d₀ → e₀` the split is at `x = α d₀` and
    `y = σ⁻¹ e₀`, inside `K`, and every turn survives. Their step hides `K′`, so this module rebuilds it from their
    interface lemmas, keeping a proper source arc.
  - `exists_firstTurnStepSection_of_turn` and `_of_goodCorners`.
  - `pocketPinchGoodCornerStepSection`: the good-corner step with properness, closed.
  - `PocketPinchLabelledFirstTurnSectionStatement`: `K.FirstTurns` in place of `K.ClosedWalk`. It is implied by the Section
    binder.
  - `PocketPinchStepFirstTurnSectionStatement` and the induction from it.
- **CLAIM: the corner reduction**, a new module `Estimating/OsinPocketGoodCornersSection.lean`, after FirstTurnSection lands.
  - Statement: under the Section premises, a pocket in first-turn order with a proper source arc has an O-equivalent copy with
    letter labels and good corners, still in first-turn order, with the same repeated visits and a proper source arc.
  - Route: `faceEdgeDoublingInside` (ghw-assembly) at each bad cycle dart, with first-turn order carried by ms-intro-4's
    `faceEdgeDoublingInside_firstTurnChain`, then induction on the number of bad darts.
  - Paper model test:
    - A cycle dart `d` has its face inside `K`. Good corners fail only when that face is a relator face, or when it holds a
      second cycle dart.
    - In both cases the face has more than one dart: relator words have length at least `ρ ≥ ρ₀ ≥ 2` by `OsinCCondition.long`,
      and two distinct darts give length two. So the doubling applies, and monogon faces never need one.
    - After doubling at `d`, the dart `embed d` lies alone on the new digon (a G-face). Faces of the other cycle darts are
      unchanged or shrink, so the number of bad darts strictly drops.
    - Configuration A `lobeDiagram` (the calibration case): cycle `[5,3,4,6]`, with darts 3 and 4 on the relator cell `a`.
      Doubling 3 and then 4 gives good corners.
  - **Monogon faces carrying a cycle dart** (paper model test, main's item 4). No counterexample found.
    - Relator monogon: its word has length 1, while `OsinCCondition.long` forces words of length `ρ`. With `ρ₀ ≥ 2` in the
      prefix of the reduction, this case cannot occur. Without `long` it does occur: `OsinPocketWrapRose`'s `R = [5]` has a
      one-letter word.
    - G-face monogon: it holds exactly one dart, so it shares no face with another cycle dart and is not a relator face. That
      corner is already good, and no doubling is needed.
    - So the reduction needs long relator words, which the Section prefix supplies, and never has to double a monogon.
      Monogon doubling (ghw-assembly's `MonogonDoubling` next step) is not on this route.
  - A fact for the step: a split can merge the faces of two cycle darts, so good corners do not survive a step. The reduction
    runs again before every step. `PocketPinchStepFirstTurnSectionStatement` takes first-turn order and a proper source arc,
    not good corners.
- **LANDED 096d9219c** (probe 0913-213157-25846 GREEN; unwired, queued for wiring). After the 23:12 resume, the tree md5 was
  checked against the probed bytes and no import had changed.
  - `Estimating/OsinPocketPinchFirstTurnSection` contains:
    - `exists_firstTurnStepSection_of_turn` and `_of_goodCorners`;
    - `pocketPinchGoodCornerStepSection`, which is closed;
    - `PocketPinchLabelledFirstTurnSectionStatement` (implied by the walk-order Section binder, by `_of_section`), and
      `PocketPinchStepFirstTurnSectionStatement` with the induction `_of_step`.
  - `Estimating/OsinPocketPinchFirstTurnAssembly` contains:
    - `SectionPocketFaceSetFirstTurnInput` and `OsinSectionPocketFaceSetFirstTurnSectionStatement`, with `.toProperInput` and
      `.toProper`;
    - `sectionPocketCutInput_of_residualsFirstTurnSection` and `osinSectionPocketCutSection_of_residualsFirstTurnSection`.
    - This is the FirstTurns producer target of w1-binder-3, per main's ruling (b).
- **Absorbed ms-intro-4's item (b)** (coordinator, 23:12).
  - Moved `GGT/VanKampen/SurgeryFaceEdgeDoublingFaces.lean` and `Estimating/OsinPocketCellGoodCorners.lean` into this lane's .files.
    Both lists are backed up under `backup/w1-binder-7/*.absorb-by-w1-binder-7.*` and `*.pre-absorb.*`.
  - Both drafts were GREEN under ms-intro-4's record 0913-214617-61792 at the same md5 (e0fcb186 and a06a9eae), with attic
    1bd896ef4. They are re-probing under this lane.
  - The cell endpoint `cellPocketPinchFirstTurns : CellPocketPinchFirstTurnsStatement` needs only first-turn order, letter labels
    and relator words longer than one letter.
- **LANDED 6029467d9**, the two adopted modules (probe 0913-232249-13380 GREEN under this lane; md5s e0fcb186 and a06a9eae
  equal ms-intro-4's green record 0913-214617-61792). Both are unwired and queued for wiring.
  - `GGT/VanKampen/SurgeryFaceEdgeDoublingFaces`:
    - `FaceEdgeDoubling.faceOf_diagram_embed_dart` and `faceOf_diagram_embed_of_ne`;
    - `exists_relatorCell_of_mem_diagram`;
    - `CornerCount.one_lt_length_of_relatorCell`, `one_lt_length_of_mem_ne` and `countP_lt_countP_of_imp`.
  - `Estimating/OsinPocketCellGoodCorners`:
    - `CellPocketFaceSet.BadCorner`, `badCorners`, the three count lemmas across `faceEdgeDoublingInside`, and
      `exists_goodCorners`;
    - `exists_simple_of_firstTurns`, `copyRegion_of_firstTurns`, and `cellPocketPinchFirstTurns :
      CellPocketPinchFirstTurnsStatement` (closed).
- **2026-09-14 ~00:10: binder 7 CLOSED in first-turn form.** LANDED 4a52b36f1 `Estimating/OsinPocketGoodCornersSection`
  (probe 0913-233843-93828 GREEN, BUILT; unwired, queued for wiring). The first push failed while github DNS was down, so it
  was landed after connectivity returned.
  - `pocketPinchFirstTurns : PocketPinchFirstTurnsStatement` and
    `pocketPinchLabelledFirstTurnSection : PocketPinchLabelledFirstTurnSectionStatement`. Both pass `#audit_closed_axioms`.
- **Route 3 (main, 00:0x).** w1-binder-3 proved first-turn order ⇔ outer following, and the proper-arc lake admits no
  first-turn order (e6f869a04), so the FirstTurns producer is blocked at map level. The pinch therefore takes walk order.
  - In flight: `Estimating/OsinPocketPinchOuterDispatch`.
    - `PocketOuterPinchStepSectionStatement`: one step at an outer pinch (walk order, `¬ K.FirstTurns`, a proper source arc,
      pinched), under the Section premises. w1-binder-3 proves it; the interface was proposed to it in one message.
    - `pocketPinchLabelledSectionStatement_of_outerPinchStep`: the walk-order Section binder, by induction. In first-turn
      order it closes outright, an unpinched pocket is simple, and otherwise the outer step applies.
  - **Interface agreed with w1-binder-3 (00:3x), with its amendment 1: a proper target arc.** At an endpoint of a target arc
    that holds the whole exterior boundary, the outer corner is the exterior. No O-equivalent split merges it with a G-face,
    and `outerSpurThickening` needs the target arc to avoid `α w_j`. Splits and corner fixes keep both arcs.
    - Rewritten dispatch module (attic f9a3d8af1, md5 b9a428ad):
      - `PocketOuterPinchStepSectionStatement`, which now takes and returns `K.targetArc.length < (outerDarts X).length`;
      - `PocketPinchLabelledSectionTwoArcStatement`, the walk-order Section binder with proper `t₁` and `t₂`, with
        `_of_section` from the landed `t₁`-only binder;
      - `pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep`, the dispatch;
      - `SectionPocketFaceSetTwoArcInput`, `OsinSectionPocketFaceSetTwoArcSectionStatement` and
        `osinSectionPocketCutSection_of_residualsTwoArc`. Proper `t₂` has to come from the top: section count ≥ 2 gives
        it, and main's route-1 test covers count = 1.
    - w1-binder-3 proves the step. It packages it with `exists_pinchStepSection_of_avoids`, adds its own variant
      `exists_pinchStepSection_of_isolated` for three or more visits with mixed turns, and reports fully crossing vertices as
      a residual.
  - **LANDED f81311dc9** (probe 0914-005613-42051 GREEN, BUILT for both modules; unwired, queued for wiring). Before the
    green attempt, five failed on MSI infra and two pushes on github DNS.
    - `Estimating/OsinPocketFirstTurnsProperArc`: `PocketFullArc.rel_of_isChain_append` and
      `PocketFaceSet.sourceArc_lt_of_firstTurns K hK hrest`.
    - `Estimating/OsinPocketPinchOuterDispatch`, the two-arc interface above:
      - `PocketOuterPinchStepSectionStatement`;
      - `PocketPinchLabelledSectionTwoArcStatement` with `_of_section` and `_of_outerPinchStep`;
      - `SectionPocketFaceSetTwoArcInput` with `.toProperInput`, and `OsinSectionPocketFaceSetTwoArcSectionStatement`;
      - `sectionPocketCutInput_of_residualsTwoArc` and `osinSectionPocketCutSection_of_residualsTwoArc`.
  - Binder 7 in walk order now rests on two open statements: w1-binder-3's `PocketOuterPinchStepSectionStatement` and the
    two-arc producer `OsinSectionPocketFaceSetTwoArcSectionStatement`.
  - Cell mirror (main approved, ~01:3x). In flight: `Estimating/OsinPocketCellPinchOuterDispatch` (attic 8f985e533, md5
    2ece7c80, probing in a retry loop).
    - `CellPocketOuterPinchStepSectionStatement`: one step at an outer pinch of a cell pocket (walk order, `¬ K.FirstTurns`,
      both arcs proper, pinched), under the Section premises. w1-binder-3 proves it.
    - `cellPocketPinchSectionStatement_of_outerPinchStep`: `CellPocketPinchSectionStatement` from it. The first-turn case
      goes through `CellPocketFaceSet.exists_simple_of_firstTurns`.
    - One spelling agreed with ms-cite-1 in one message. The dispatch concludes exactly `CellPocketPinchSectionStatement`,
      which ms-cite-1's consumer `…_of_pinchSectionOrderEuler` reads. Its cell-walk proper-arc residual delivers the two
      premises of `CellPocketPinchSectionInput`: `firstArc.length < (cellDarts X i).length` and the same for `secondArc`.
    - **LANDED 117d5d3c3** (02:06; probe 0914-014352-5149 GREEN, BUILT; unwired). `cellPocketPinchSectionStatement_of_outerPinchStep`
      closes V5 residual 7 over w1-binder-3's cell outer step.
- **Resume 2026-09-14 08:4x, after the laptop reboot wiped /private/tmp.** The rebuilt infra is at `f907d0cb…/scratchpad/nm`.
  - Every w1-binder-7 SHA was already on origin, so there was nothing to re-probe. The lost green records only matter for
    future landings.
  - Re-added this lane's 16 module paths to `.files`.
  - Re-queued wiring for the 14 unwired landed modules, in import order. `OsinPocketTrimDouble` and
    `OsinPocketPinchStepSection` are already wired.
  - State:
    - binder 7 in first-turn form: closed (4a52b36f1);
    - walk-order binders 7 and 5: depend only on w1-binder-3's two outer steps (`PocketOuterPinchStepSectionStatement`,
      `CellPocketOuterPinchStepSectionStatement`) and the proper-arc producers.
  - New item (main, ~08:4x): prove the cell outer step `CellPocketOuterPinchStepSectionStatement`. w1-binder-3 keeps the section
    one.
- **CLAIM: `Estimating/OsinPocketCellOuterPinchStep.lean`**, the cell outer step.
  - Route: the split outside `K` at an isolated turn, reusing w1-binder-3's `PinchSplit.Input.TurnKept` and
    `OuterPinchIsolated.*` from its unlanded `OsinPocketOuterPinchSplit` / `…Isolated`. A list-level form of the isolated-turn
    lemmas was requested from w1-binder-3 in one message.
  - Cell transports: `CellPocketFaceSet.pinchSplit` with `pinchSplit_repeatedVisits_lt_of_stretch`, and a new
    `pinchSplit_closedWalk_of_isolated`. Both arcs stay proper, since the split carries relator words.
  - Corner fixes at cell corners:
    - a relator corner: `CellPocketFaceSet.faceEdgeDoubling` on a dart off both arcs, which properness gives, or
      `exists_trimDoubleFirst/Second` when a side has room;
    - an exterior corner: a cell transport of `outerSpurThickening`. None exists; a cell pocket has no target arc.
  - **Model test (paper, 09:0x): the full-boundary wrap on the cell side is excluded by properness, and no other obstruction
    was found.**
    - Conventions:
      - The corner after `z` belongs to `faceOf (α z) = faceOf (σ z)`.
      - Doubling `w` puts the digon next to `w` at both ends: the corner after `α w`, and the corner before `w`.
      - A corner after a cycle dart lies outside `K`; a corner after the reversal of a cycle dart lies inside `K`.
    - At an isolated turn `d₀ → e₀` the merged corners lie after `x` (in the sector after `e₀`) and after `y` (in the sector
      before `α d₀`). Both are outside `K`.
    - A relator corner there:
      - Corner after `e₀`, when `e₀ = α a_n` ends the reversed first arc: it lies on cell `i` between `a_n` and `a_{n+1}`.
        Doubling `σ e₀ = a_{n+1}` fills it, and `a_{n+1}` is off the arc exactly when the arc is proper.
      - Corner after `y`, when `σ y = α d₀ = a_1` starts the arc: doubling `α y = a_0` fills it, and `a_0` is off the arc
        by properness.
      - A corner of another relator cell: doubling `σ e₀` or `α y`, with no arc condition.
    - Interior arc vertices never host the cell corner of an isolated turn. The cell corner there is the one-step sector
      `α a_k → a_{k+1}`; its turn `α a_{k+1} → α a_k` sweeps the long way round, past every other cycle edge at a pinched
      vertex, so it is not isolated.
    - The wrap: when an arc is the whole cell boundary, `a_{n+1} = a_1` lies on the arc and the doubling is blocked. This is
      the cell form of w1-binder-3's amendment 1, and the proper-arc premises exclude it. Relator words have at least
      `ρ ≥ 2` letters, so no doubled face is a monogon.
    - **`i ≠ j` (checked 09:1x): the producer supplies it.** When both arcs lie on one cell, `σ e₀` can lie on the other arc
      and block the doubling. binder 5's producer `exists_of_joinsCells_closedWalk` takes `hij : i ≠ j`. So the cell step is
      stated additively with `i ≠ j`:
      - `CellPocketPinchSectionDistinctInput` and `CellPocketPinchSectionDistinctStatement`, with `_of_section`;
      - `CellPocketOuterPinchStepSectionDistinctStatement` and its dispatch;
      - `copyRegion_of_pinchSectionDistinct`.
      - ms-cite-1 was asked, in one message, to point its consumer at the Distinct form.
    - CLAIM `Estimating/OsinPocketCellOuterSpur.lean`: `CellPocketFaceSet.outerSpurThickening`, the cell transport for
      exterior corners. It needs no avoid hypothesis, since a cell pocket has no target arc.
    - Exterior corners need a cell transport of `outerSpurThickening`, which this lane builds.
  - No current item otherwise.
- **Noted:** ms-cite-1's `cellPocketPinchRoseRefutation` (e0a0776bb) refutes `CellPocketPinchPosStatement`, so V4 endpoints over
  it are vacuous. The replacement is `CellPocketPinchSectionStatement`.
- **Landed above (was in flight): `Estimating/OsinPocketGoodCornersSection`** (attic 12585faa5), the section mirror.
  - `PocketFaceSet.BadCorner`, `badCorners`, the count lemmas, `exists_goodCorners` and `exists_simple_of_firstTurns`.
  - `pocketPinchFirstTurns : PocketPinchFirstTurnsStatement`: over relator words longer than one letter, a pocket in first-turn
    order with letter labels has a copy with a simple pocket face set. It needs neither least area nor a proper source arc.
  - `pocketPinchLabelledFirstTurnSection : PocketPinchLabelledFirstTurnSectionStatement` at `ε₀ = 0`, `ρ₀ = 2`, through
    `OsinCCondition.long`. If it lands green, binder 7 is closed in its first-turn form.
- **w1-binder-3's heads-up** (23:3x): walk order does not give `K.FirstTurns` at map level. Evidence: w1-binder-4's
  `OsinPocketCellFirstTurnsLakeModel`, where the source cell lies in a lake attached at one vertex and the first-turn predecessor
  has two orbits. So any FirstTurns producer must change the diagram or the face set. w1-binder-3 targets
  `SectionPocketFaceSetFirstTurnInput` as landed and reports the producer as blocked on that choice.
- **Next after GoodCornersSection:** `PocketFaceSet.sourceArc_lt_of_firstTurns` (FirstTurns forces a proper source arc), so the
  producer's properness clause comes for free.
- **Earlier plan, now in flight above: `Estimating/OsinPocketGoodCornersSection`**, the section mirror of the cell module.
  - `BadCorner`, `badCorners` and the count lemmas across `faceEdgeDoublingInside`, which also keeps a proper source arc.
  - `exists_goodCorners`.
  - `pocketPinchStepFirstTurnSection`, which should prove `PocketPinchStepFirstTurnSectionStatement` at `ρ₀ = 2`.
  - `PocketFaceSet.sourceArc_lt_of_firstTurns`: FirstTurns forces a proper source arc. This is ms-intro-4's paper finding,
    which this lane checked.
- **Resume 21:22 (after the session limit).**
  - The FirstTurnSection probe 0913-203127-13291 lost its msi hop (rc 255), so no record was written. Its SLURM job built
    successfully (log: `Build completed successfully (10285 jobs)`).
  - The tree md5 e1cea1ea equals attic 76331da9e, and no import had changed since its base. It is re-probing together with
    `Estimating/OsinPocketPinchFirstTurnAssembly` (w1-binder-3's producer target) so that a record is written.
- ms-intro-4 (binder 5, `CellPocketPinchPosStatement`) imports ArcTrim and FullArc; their helper names stay fixed. There is
  no generic boundary-cycle layer, and `exists_trimDouble` is at `PocketFaceSet` level.
- Where the step route sticks: a full arc with a nonempty remainder and both sides at length exactly `ε`. No trim has
  room, and transport surgery keeps arcs and sides. This does not refute the Prop, since the conclusion may change the
  source, the kept cell, the arcs and the sides.

## For the waist owner (ghw-assembly), through the lead

The one-line swap in `relativeGreendlingerQuasiGeodesicLeastArea_of_openResiduals` (`OsinGreendlingerOpenResiduals`):
- replace binder 7 `hpinch : PocketPinchLabelledStatement` with `hpinch : PocketPinchLabelledPosStatement`;
- call `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsPos` instead of `_of_residuals`.

That removes the false binder from the waist. hull-respell's step route then targets `PocketPinchStepPosStatement` through
`pocketPinchLabelledPosStatement_of_stepPos`. The `ε ≥ 1` truth of the repaired pinch is not settled in general. The rose is
only the known counterexample shape, and it is rescued.
