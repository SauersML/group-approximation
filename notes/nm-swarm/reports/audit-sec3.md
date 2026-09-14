# audit-sec3 lane report

Lane `audit-sec3` audits tex 785–1620 of `non_mf_groups_exist.tex`: Section
`sec:one-sided-inverses` (tex 785–1323) and Section `sec:amenable-nonqd` (tex 1324–1620).

## Landed

- `3ae281ab9`: the first version of `GroupApproximation/Manuscript/NonMF/Audit/Sec3.lean`, the
  permanent gate for tex 785–1323. No green probe built it. The probe that named it,
  `0913-025304-66495`, failed (rc=1).
  - The wire queue's 03:13 entry for it wrongly said GREEN and is withdrawn.
  - `80abe6604` supersedes it.
- `b9772f360`: probe GREEN (tag `0913-030424-12674`, BUILT both modules), bytes identical to
  main, both wired:
  - `GroupApproximation/Manuscript/NonMF/Audit/Sec4.lean`, the permanent gate for tex 1324–1620.
  - `GroupApproximation/Manuscript/NonMF/AffineDoublingLiteralModel.lean`, the carrier of defect 2
    below.
- The landing that carries this report: probe GREEN (tag `0913-040726-62527`, BUILT `Audit.Sec3`; the carrier's bytes are
  those BUILT at `0913-035646-36298`). Both
  modules are on the wire queue, carrier first:
  - `GroupApproximation/Manuscript/NonMF/RingCompressionCellGeneral.lean`, the carrier of defect 1
    below.
  - `Audit/Sec3.lean`, regenerated from the census at origin/main `42d443298`, with the new
    carrier and the rows the jacobson and leavitt-units lanes have filled since.
  - The row corrections `metadata/nm-census-rows/audit-sec3.tsv`.
- `494dc3249`: `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketLakeLabelledModel.lean`,
  probe GREEN (tag `0913-155026-81505`, BUILT, bytes identical to main), queued for wiring. See
  "Configuration B labelled model" below.

## The rows in range

The census has 254 rows in range: 202 formalized, 26 definition, 17 structural, 6 partial and
3 attribution.

1. **Reachability.** Every declaration named by the 228 formalized and definition rows exists on
   origin/main in a module the root reaches, and so does every declaration the row corrections
   add. The exception is `RingCompressionCellGeneral`, which is on the wire queue.
2. **Gate.** Each gate runs `#audit_closed_axioms` on every named-Prop endpoint and every closed
   theorem the census names in its range, and `#audit_axioms` on every other named declaration:
   - `Audit/Sec3.lean`: 130 `#audit_closed_axioms` and 177 `#audit_axioms`, covering 269
     distinct declarations. A declaration named by several rows is audited once per row.
   - `Audit/Sec4.lean`: 29 `#audit_closed_axioms` and 90 `#audit_axioms`, covering 102 distinct
     declarations.
   - Every import of `Audit/Sec3.lean` except the new carrier is in the root import closure at
     origin/main `07169dd31` (6217 modules, no dangling import). `Audit/Sec4.lean` is wired.

   The gates also cover the claim-making structural rows and the declarations the row corrections
   add.
3. **Reading against the print.** The carriers checked in detail:
   - `lem:ring-compression-cell` (tex 855–912): defect 1.
   - The concrete instance after `prop:clifford-locally-rf` (tex 1589–1610): defect 2.
   - Proof of `thm:full-defect-ring` (tex 936–943):
     - `EJZCitationSentences.PrintedUniversalRingBothGroupsPropertyT` states property (T) at the
       printed `G = EL₄(𝒞)` (`UniversalGroupB.B`) and at the printed `L`, the core on coordinates
       1,2,3.
     - It also states the surjection onto `L_{𝔽₂}(1,2)`, nontriviality, finite generation of `𝒞`
       and finite generation of `G`.
     - The theorem is closed, so neither `[EJZ, Theorem 1.1]` nor `[BHV, Theorem 1.3.1]` enters as
       a binder.
   - The Jacobson paragraph (tex 1122–1145, jacobson lane):
     - `PrintedJacobsonRadical` states `Rad_MF(EL_n(J)) = EL_n(J,JeJ) ≅ ⋃_N SL_N(𝔽₂)`, infinite,
       simple and locally finite, for `n ≥ 4`, as printed.
     - `PrintedJacobsonKernelFinitary` binds `2 ≤ n`, the range in which the paragraph uses
       `EL_n`. Its third clause ("acting on `V^n` as all of `GL_fs(V^n)`") needs a second
       coordinate.
     - `manuscriptSentence_jacobsonShiftAction` and `manuscriptSentence_jacobsonQuotientLaurent`
       state every clause of their sentences.
     - `blockAct_elGen_matUnit` gives the relative roots.
     - `blockAct_commutator_matUnit` gives the commutator
       `[e_ik(f_uw), e_ki(f_wv)]` at `w = v`, one witness for the printed "the commutator … of
       two".
   - Proof of `cor:leavitt-mf-quotient` (tex 1307, leavitt-units lane):
     - `PrintedKhanhThanhSentence` is stated for every field, which covers the printed countable
       field. It states all five clauses, and `[KhanhThanh, proof of Theorem 7.2]` is proved, not
       assumed.
     - `PrintedLeavittBothInclusions` states both inclusions and the triviality of every
       homomorphism from `EL_d(R)` to an MF group, for every countable field and every `d ≥ 2`.

## Defects

1. **Fixed: rows `718cc7b04afd` (L872), `c0383f82a141` (L888), `d1142160bf17` (L899) and
   `83ed5eb3b38c` (L904).**
   - `lem:ring-compression-cell` is printed for every unital ring `R` and every `s, t ∈ R` with
     `ts = 1`. The census carriers `FullDefectRingSentences.manuscriptSentence_compressorPieceDef`,
     `…_compressorInvertible`, `…_centralMark` and `…_centralMarkCentral` are stated only at
     `UniversalPair.pairInverse`.
   - `RingCompressionCellGeneral` states and proves each sentence for every ring and every
     `P : OneSidedInverse R`:
     - `printedCompressorPieces`: `u_i = e_{4i}(t-1)e_{i4}(1)e_{4i}(s-1)e_{i4}(-t)`.
     - `printedCompressorInvertible`: `u = u₃u₂u₁` is the displayed matrix, and that matrix is
       invertible.
     - `printedCentralMark`: `c = [e₄₁(e), e₁₄(t)] = diag(1,1,1,1+et)`.
     - `printedCentralMarkCentral`: `c ∈ C_G(L)`, along the printed route. Every element of `L` has
       the shape `diag(A,1)` (`core_isBlockDiagOne`), and `diag(1,1,1,1+et)` commutes with every
       such matrix (`centralMarkMatrix_commute_blockDiagOne`).
   - The row corrections name the new carriers first and keep the universal-pair instances.
2. **Fixed (`b9772f360`): rows `3229365c29c6` (L1589), `e947a3d4f4a1` (L1598), `80c65e0771e4`
   (L1608) and `c48c7da870a2` (L1608).**
   - The carriers of "`α(v,A) = (2v,A)`" and of "its image consists of the affine matrices whose
     translation coordinates are all even, so `[Γ̄ : α(Γ̄)] = 8`" were proved on
     `Monsters/AffineSL3Doubling.lean`. That is a separate semidirect product whose `alpha` is
     defined by doubling, so they say nothing about `ExplicitLinearModel.gammaBar` and `conjD`.
   - The display of `Γ̄` and the definition of `D` and `α` named no declaration.
   - `AffineDoublingLiteralModel` states and proves all four on `gammaBar ≤ GL₄(ℚ)` and conjugation
     by `dU`.
3. **Fixed by row correction: definition rows that named no declaration.** They are
   `5870021d2e03` (L806), `18fd64bafd97` (L1039), `60898a519f4f` (L1435), `c180c0186454` (L1435),
   `bc2d73bb124a` (L1539) and `e4ebdec3bbab` (L1548). The corrections name the declarations that
   carry the printed setup. The leavitt-units lane filled `dcf6fa4be4de` (L1298).
4. **Fixed by row correction: `77028123cdd6` (L1598).** The row named only
   `gammaBar_residuallyFinite`. The clause "it has property (T) [BHV, Example 1.7.4(i)]" is the
   closed `CommutingLampCollapse.gammaBar_hasKazhdanPropertyT`.
5. **Fixed by row correction: claim-making structural rows that named no declaration.** They are
   `19abb698ab4a` and `3a929e3e1455` (L788), `ded89cfcd0e4` (L1239), `d47b613bb096` (L1384) and
   `8e53d32e3fb8` (L1435).
6. **Fixed by row correction: rows naming only a `def … : Prop`, never the theorem that proves it.**
   They are `2ff745dd7064` (L1060), `eefa8a852d05` (L1239), `7ce8c636a470` (L924) and
   `18fd64bafd97` (L1039). Each correction adds the `…AllCharacteristics` theorem of
   `FullDefectRingEJZUnconditional` whose type is that Prop.

## W1 model tests (lead item, 2026-09-13 after the 08:30 restart)

The item: model-test and truth-audit the piece Props of W1 `hgreendlinger`, meaning the h94
pieces and the Euler-count chain. dgo-geometric covers the pocket Props and C3–C5.

1. **Landed `594d1e97a`: `GGT/VanKampen/Estimating/OsinCConditionLineModel.lean`.** Probe GREEN
   `0913-093823-13550` (BUILT); it is on the wire queue.
   - `D` is `ℤ` with alphabet `{±1}` and no subgroups, and it is 0-hyperbolic (`hyperbolic`).
   - `condition`: `{a^m, a^-m}` satisfies `OsinCCondition` whenever `λ ≤ 1`, `0 ≤ c`, `ρ ≤ m`
     and `2ε < μ m`. Since `ℤ` is abelian, the exclusion clause forces two different connectors,
     so every piece is shorter than `2ε`.
   - The closed endpoint `osinCConditionLineModel : OsinCConditionLineModelStatement` holds for
     every `0 < λ ≤ 1`, `0 ≤ c`, `0 < μ`, `ε` and `ρ`. So the C-condition layer of every piece
     assumption can hold at every threshold.
   - The earlier models on main, `UnboundSmallMuCounterexample.condition` and
     `UnboundConjugateCounterexample.condition`, fix `ε = 0` and one `ρ`.
2. **Case 1 (theoremc-retire): closes; the composition is not landed.**
   - `OsinLemma94CaseOneWalkStatement` is true as landed at `fd6ce3c09`.
     - `a < a'` is `source_forward`; `b' < b` is a hypothesis.
     - `walk` and `closed` give the two value equations.
     - `boundary_arc` puts the target inside one section.
     - Allowing any connector alphabet is harmless, because the conclusion names no connector
       word.
   - ko-closed proved it: `osinLemma94CaseOneWalk`, GREEN `0913-095509-55850`, bytes = main
     `8f0f73966`.
   - `osinLemma94CaseOneInput_of_walk` is GREEN `0913-093623-11190` at the bytes of `3292f7a20`.
     Composing the two proves `OsinLemma94CaseOneInput`, but no landed declaration composes them.
   - `OsinLemma94CaseOneSameCellStatement` is redundant.
     `RealizedSectionFamily.false_of_quadrilateral_face` has no hypothesis that the source and
     target cells differ, so `osinLemma94CaseOne_false_of_walk` already covers pairs whose sides
     have the same kind.
3. **Case 2 surgery (hull-unbound, sec5-sentences): no counterexample.**
   - `PendantPathRemovalInput`: `DegreeTwoJoints` makes the path a spur from a leaf. A spur that
     was a whole component would make the face the exterior.
   - `CornerInsertionInput`: a chain with the face on both sides cannot close up, so the inserted
     word splits the face into two unselected `G`-faces.
   - `SeparatingPathRemovalInput` is proved from the pendant form (`7d4a2515f`).
4. **Count piece (hull-count94).**
   - `OsinLemma94PolygonCoversInput` is closed, with `L = 24ε` (GREEN `0913-093648-12289`).
   - `OsinLemma94PolygonSideBudgetInput` is plausibly false, through the outward-spur mechanism
     hull-count94 reported. The candidate instance is below. It was sent to main, which holds
     the ruling.
5. **The Euler-count chain.** C1 `phiSubdividedMultigraphO` (`4e27d4965`), C2
   `card_add_six_le_of_linkedO` (`050822843`) and ghw-charp2's `hlinked` and `hV` producers are
   unconditional, and `DartMinimal` is sound.
6. **C6′ `TwoGonHoldsInput` (`4beca2743`).** Not audited in this item. The next lead item
   audited it, in the section "Lemma 9.3 piece Props and P2".

### Candidate counterexample to `OsinLemma94PolygonSideBudgetInput`

- **Setup.** `G = ℤ` with base alphabet `{±1, ±2}` and no subgroups; `λ = 1/2`, `c = 3`;
  `W = {1^m, (−1)^m}`.
- **Boundary word.** `u · (−1)^m · (−1)^{6t}` with `u = (2 2 2 1 −1)^t`. Its three sections are
  `(1/2, 3)`-quasi-geodesic.
- **Diagram.**
  - a `G`-face `f` with walk `2^{3t} (−1)^{6t}`, of value 0;
  - `t` outward spurs `1 −1`, rooted on the `2`-side of `f`;
  - one relator cell `(−1)^m`, at the far corner.
- **Why the hypotheses hold.**
  - With one cell, `Reduced` holds vacuously.
  - The boundary value is `−m ≠ 0`, so `LeastArea` holds.
  - No cell dart is on the walk of `f`, so `f` lies in no region. `f` cannot fold, since its
    labels are `2` against `−1`.
- **The polygons.** One polygon, and every side is an arc of `outerDarts`. Each spur root is a
  vertex of degree 3, where `facePerm (alpha e') ≠ alpha e`, so `Maximal` allows a split there.
  `short_region` cannot absorb these sides. So `∑ sideCount ≥ t + 1`, against `K n = K`.
- **Unverified.**
  1. Some optimal family on this diagram has card at most 9.
  2. The dart-minimal optimum keeps the spur roots on polygon walks. Every O-equivalent diagram
     reads the same word, and its `t` letters `1` allow at most `t` bridges.
- **Consequence.** The count grows with the section length `t` at every `ε`, `ρ` and `n`, so
  moving `∃ K` after `∀ ε` does not repair the Prop. Letting (A2) sides skip value-one excursions
  does.
- **Declined by the lead (~13:10).** A formal fixture for this instance is not wanted: the F1
  ruling already includes (A2), no splits at value-one excursions, and hull-count94 has the
  instance. The one-cell `LeastArea` nonvacuity model over the line model is skipped too.

## Lemma 9.3 piece Props and P2 (lead item, 2026-09-13 ~11:40)

The item has two parts:
- The three Props that hull-euler's assembly `phiPrimeCountInput_of_smallFaces` (`4beca2743`)
  takes: say whether each is true at the fixed parameters as stated, or give a model where it
  fails.
- The same for kh-ejz's sides theorem P2.

The verdicts went to the owners and to the lead at about 13:05. Nothing fails as stated.

1. **C4 `CornerTwoGonInput` (leavitt-units, `d0a41c1da`): true for every `E` and `P`; not
   proved.**
   - A two-gon face whose gap holds a corner sits at `O`, between consecutive exterior regions
     `a` and `b` of `E`. Its gap runs from the end of `a`'s target arc to the start of `b`'s.
   - Target arcs of different regions are disjoint in position, so the gaps are pairwise disjoint.
     The arcs are disjoint because:
     - the face of a target-arc dart lies in its region;
     - `P.pairwise` makes the face sets disjoint;
     - `P.nondegenerate` makes every arc nonempty;
     - an arc stays inside one section.
   - Sending a face to the corner its gap holds is injective into the `count` corner points.
     `cut_zero` and `cut_last` name the same point, so the card is at most `cuts.count`.
   - The assembly instantiates C4 at `E := linkedComponentO S.family a₀` through `P.mono`. This is
     sound: the Prop quantifies over every `E` and `P`, and `hcorner` and `hsmall` receive the same
     `P'`.
2. **C5 `CellFaceCountInput` (hs-vanishes): proved.** `cellFaceCountInput` (`a6a2cadda`), probe
   GREEN `0913-100213-68371`, bytes = main.
3. **C6′ `TwoGonHoldsInput` (debt-conditional; hull-euler's assembly): true; the gap orientation is
   right; not proved.**
   - Orientation. `σ` at `O` runs through decreasing positions, so `GapAtOHoldsCorner` reads the
     pocket-side gap. When `E` has two regions, the other face is the wrap gap, which holds corner
     0 by `cut_zero`.
   - With no corner in the gap, `a` and `b` target one section.
   - A two-gon between two cells contradicts `NoMultipleEdges`. `NoLoops` and `P.noLoop` exclude
     loops, so LoopCut ruling (A) adds nothing.
   - `¬HoldsCellO` leaves no cell and no other region in the pocket. So `a ∪ pocket ∪ b` beats the
     family, in `S.diagram` or in an O-equivalent copy. Both optimality clauses range over every
     realized family of the same `Delta`.
   - Formal debt:
     - No landed theorem has type `TwoGonHoldsInput`. The closing pieces are over `S.diagram`:
       `emptyTwoGonInput_holds` (`OsinPocketDiscEmptyTwoGon`, `2aa17abb0`) and `false_of_zeroCellPocket`
       (`ce1028aa1`). Both take a `PocketRegion` whose complement cycle reads the merged
       decomposition.
     - `S.diagram` has no such region in three configurations:
       - (a) a section backtrack between the targets;
       - (b) a source-gap edge with cell `i` on both sides;
       - (c) `a.rightSide` and `b.leftSide` sharing an edge behind cell `i`. The union is then an
         annulus around cell `i`, with the shared edge inside it.
     - Ruling (B) (`bdc7337fd`) names only (a) and (b). kh-ejz's report says `Γ₁` avoids (c). That
       holds for the pocket walk, but not for the union the zero-cell merge needs, so (c) also
       reaches the kept cell of `SectionPocketFaceSetInput`. A face-edge doubling in `a`'s face gives
       a copy where the union is a pinched disc. That copy needs a transport of `a` and `b`, since
       `SurgeryFaceEdgeDoublingRegions` carries only regions that avoid the doubled face and the
       face across.
     - Ruled this way by the lead (~13:25), after `dfb09b83f`: configuration (c) takes
       "FaceEdgeDoubling in x's face, plus a transport of x and y".
     - Pinched unions. `noncrossingClosedWalkSides` gives only a `BoundaryCycle`, and
       `bothFollowUnpinched` (`74d4ebd34`) needs `FollowsBoundary` on both cycles. So no landed
       declaration builds a `PocketRegion` from a pinched walk. `PocketPinchPinchedStatement`
       (`OsinPocketPinchUnpinched:61`) still has no producer. `toPocketFaceSetOfNoncrossing`
       (`aa2df0eaa`) gives a `PocketFaceSet` in walk order, not a `PocketRegion`.
     - The turning condition and `alpha_not_mem` for the pocket walk on the copy are open (kh-ejz
       report, item 5). `37957f19b` checks them only on the pinched model `[5,3,4,6]`.
   - This verdict first went to hull-euler only, because I read the lead's "(debt-conditional)" as
     a status. It names the owning lane, so `debt-conditional` received the verdict too.
4. **P2 `NoncrossingClosedWalkSidesStatement` (kh-ejz, `26a7858f2`): proved; one docstring inference
   is wrong.**
   - `noncrossingClosedWalkSides` carries `#audit_closed_axioms`; probe GREEN `0913-111928-29730`.
     `37957f19b` adds `turn_mem_of_first` and the pinched-pocket model test.
   - It is not vacuous. These pass:
     - every simple walk;
     - the touching figure-eight;
     - the pinched pocket `[5,3,4,6]`.
     The crossing figure-eight fails, since its rotation reads in, in, out, out.
   - `turn_mem` is alternation at each vertex, and it does not say which departure follows which
     arrival. A model where the walk crosses:
     - a vertex `v` with three two-edge petals, and `w = [out₁, in₂, out₂, in₃, out₃, in₁]`;
     - the rotation at `v` is `alpha in₁, out₃, alpha in₂, out₁, alpha in₃, out₂`;
     - the map is planar, with V 4, E 6 and F 4, and `turn_mem` holds;
     - the pairs `(alpha in_k, out_k)` sit at positions (0,3), (2,5) and (4,1), and interleave
       pairwise, so the walk crosses itself three times at `v`.
     The theorem still holds for this walk: `w` bounds the three petal faces. The wrong part is the
     docstring's "so the walk touches itself there but never crosses" (line 18). The statement is
     fine.
   - Consumer caveat. The conclusion is a `BoundaryCycle`, which has no chain condition. It gives no
     `FollowsBoundary`, no `FaceSetBoundary` and no `IsDiscRegion`.
   - No message with the statement came from kh-ejz; it was read on main.

## Lemma 9.4 residuals (lead item, 2026-09-13 ~13:25)

The item: say whether hull-unbound's residual Props in `OsinLemma94SectionResiduals` (`0087a5095`)
are true, false or vacuous, and whether `osinLemma94PolygonRealizationInput_of_partition` is
non-vacuous. `OsinLemma94PolygonCountInput` (audit-intro) and `OsinLemma94CaseOneInput`
(theoremc-retire) are out of scope. The verdicts went to ghw-assembly, cite-hull, sec5-sentences
and the lead at about 13:35.

1. **`OsinLemma94PolygonPartitionInput`: true, not vacuous, proved.**
   - ghw-assembly proved it: `osinLemma94PolygonPartitionInput` (`OsinLemma94PolygonPartition`,
     `746028b24`), `#audit_closed_axioms`, probe GREEN `0913-132334-2532`. No sorry, axiom or
     native_decide in `PolygonPartition`, `PolygonMaximal`, `PolygonSides` or `PolygonKinds`.
   - It is applied at real instances: `osinLemma94PolygonRealizationInput_of_pieces` produces all
     four hypotheses from closed pieces and `gFacesApart_of_dartMinimal`.
   - There is no wire-queue line yet for `OsinLemma94PolygonPartition` or its imports.
   - Fidelity note, not a truth defect. `Maximal` (`OsinLemma94PlanarPieces:205`) checks only pairs
     with `i + 1 < sideCount`, never the wrap pair `(sideCount − 1, 0)`. `baseOf`
     (`OsinLemma94PolygonKinds:76`) is the `idxOf` of the head of `outerDarts`, which is the walk
     length, so no rotation, on every face that does not contain that dart. So a run of one kind
     can be split at the base of each polygon without a turn: at most one extra side per polygon.
     Osin's sides are maximal around the whole boundary. Case 2 is proved with the linear form. The
     lead holds the routing to the count and Case 1 owners.
   - Owners of a fix, per ghw-assembly: (a) `baseOf` (ghw-assembly) and (b) `Maximal`
     (hull-unbound); (b) needs (a).
   - A model test for (b): a diagram with no relator cell whose one inner face is a cycle graph,
     with one section. The face has no turn, so its only side is the whole walk. If `Maximal` also
     checks the wrap pair, at one side that pair is `(0, 0)` with no turn, and `Maximal` fails.
     So (b) needs `2 ≤ sideCount k`, and (a) should rotate to any allowed split, meaning a turn or
     a change of kind. Sent to ghw-assembly.
2. **`OsinLemma94CaseTwoInput`: true, proved.** `osinLemma94CaseTwoInput` (`OsinLemma94CaseTwo`,
   `e0e94015d`), probe GREEN `0913-131149-5355`, on the wire queue. The Prop ends in `→ False`, so
   an unmet hypothesis is its content.
3. **`osinLemma94PolygonRealizationInput_of_partition`: its only hypothesis is proved.**
   hull-unbound's unlanded local edit of `OsinLemma94SectionResiduals` (13:30) adds the closed
   `osinLemma94PolygonRealizationInput` and plugs in Case 2, leaving `hcount` and `hone`.
4. **Non-vacuity of the `OsinLemma94PolygonRealizationInput` prefix: met on paper, no formal
   witness.**
   - Every hypothesis but one has a producer on main:
     - `OsinCCondition` at every threshold, over a 0-hyperbolic alphabet: `osinCConditionLineModel`;
     - reduced diagrams with `rCellCount` equal to the area: `cactusRealizationStatement`, through
       `exists_reduced_discDiagram_of_cactusRealization`;
     - the family: `exists_globallyDistinguishedSectionFamily`;
     - `DartMinimal`: `exists_dartMinimal`, which keeps the card.
   - The card bound `S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1)` has no closed
     producer. `PhiPrimeCountInput` rests on C4 and C6′ (items 1 and 3 above: true, unproved) and
     on the loop and multiple-edge cuts.
   - The residuals introduce no new vacuity. `UnboundInput` (`OsinAppendixSectionInduction:113`)
     and `OsinLemma94SectionStatement` (`OsinAppendixSections:315`) take the same hypothesis, and
     `osinLemma97_atParameters_of_inputs` discharges it for every family inside the induction
     (Osin, Lemma 9.7(a)).
   - On paper: past Osin's thresholds, a one-cell diagram over the line model's `W m` meets every
     hypothesis, with boundary `a^m` and `cuts` the whole word. `LeastArea` holds since
     `a^m ≠ 1`. The lead declined a formal fixture for this instance at ~13:10.

Lead ruling on the wrap pair (~15:00): `Maximal` and `baseOf` stay unchanged. The single-side
model shows that fix (b) would falsify `PartitionInput`. The extra side goes into the budget as
one class per polygon in L, and audit-intro checks it.

## W1 residual truth audit (lead item, 2026-09-13 ~15:00)

The item: give the truth of three W1 residual Props, as stated, on the models on main.
- Configuration A is the pinched two-gon (`OsinPocketPinchedTwoGonModel`, `…Lobe` `4181011af`,
  `…OuterFollows` `e533e5581`): the inner cycle fails and the outer cycle follows.
- Configuration B is the two-petal rose (`OsinPocketLakeModel` `67e5b2f9c`, map only): the inner
  cycle follows and the outer cycle fails. A labelled rose is not on main.

The verdicts went to kh-torsion, go-lemma42, hull-respell, kh-cckw and the lead at about 15:15.
They are findings only; nothing was built.

1. **`PocketCellTransportStatement` (`OsinPocketPieces:312`): true, proved.**
   - Proof: `pocketCellTransport` (`OsinPocketGlueCellTransport`, `874a332a2`), with
     `#audit_closed_axioms`.
   - Consumers: `OsinPocketCutResiduals:53,64` and `OsinDescentResiduals:50`.
   - It uses only outer following, so A is an instance and B makes it vacuous. It needs no change
     under R2.
2. **`GeodesicCollarStatement` (`SurgeryGeodesicCollar:71`): true as stated (paper sketch).**
   - Vacuous at both models: at A `hin` fails, and at B `hout` fails.
   - Sketch:
     - `bothFollowUnpinched` (`OsinPocketUnpinchedEuler`, no consumer yet) and
       `isSimpleClosedWalk_of_followsBoundary` (`OsinPocketRegionUnpinched:219`) make `s ++ rest`
       a simple closed walk.
     - `s = []` is `geodesicCollarOutput_nil`.
     - When `g ≠ []`, Strip and Insert give the G-faces `s·g⁻¹` outside and `g·q` inside.
     - When `g = []` and `rest ≠ []`, Strip and Join identify the distinct ends of `s` inside the
       strip.
   - Smallest revision if R2: delete the `P.inner.FollowsBoundary →` binder. The Prop still looks
     true, but every case, `s = []` included, then needs an un-pinch.
   - At A, splitting `{1,3,6,8}` into `{1,3}` and `{6,8}` merges `a` and `b` into `[3,4,6,5]`, and
     the walk `[5,3,4,6]` becomes simple. This is O-equivalent only when `a` and `b` are G-faces; in
     `lobeDiagram`, `a` is a relator cell.
3. **`PocketPinchLabelledStatement` (`OsinPocketPieces:272`): true at both models; general truth
   not settled (no counterexample, no complete sketch).**
   - A: `K' = lobeK` (`pinchedPocketLobeModel`).
   - B, labelled by hand with `Π = [1]` and `K = [0,2]` relator cells and `eps = 0`: the witness is
     `K'.faces = {Π}`, with kept `Π`, source `K`, sourceArc `[0]`, empty sides and an empty
     targetArc. Its boundary `[1]` is a single loop.
   - Both pass because the conclusion ties `K'` to `K` only through `(eps, lo, hi)`. That is harmless
     to `sectionPocketCutInput_of_pieces`, which reads only positions and `eps`.
   - Route finding: `PinchSplit.Input` (`SurgeryPinchSplitDiagram:61`) needs both merged corners to
     be G-faces. At both pinch vertices the complement corners are the exterior face and a relator
     cell (A: `b | ext | a | Π`; B: `Π | K | O | K`), so no Input exists there.
     `OsinPocketLakeAbsorption` (`49feec035`) needs `Π` in the exterior piece, so a lake containing
     `Π` is the open case of `PocketPinchStepStatement`.

## Configuration B labelled model (lead item, 2026-09-13 15:25)

`GroupApproximation/GGT/VanKampen/Estimating/OsinPocketLakeLabelledModel.lean` formalizes
configuration B from item 3 above. It landed at `494dc3249` after probe `0913-155026-81505`, whose
record reads `# PROBE GREEN`, BUILT the module, and holds the landed bytes (md5 `341c9283`). It is
queued for wiring and adds no census row.

- `roseDiagram` is the rose `OsinPocketLakeModel.M` (darts `Fin 4`, alpha `![1,0,3,2]`, sigma
  `![1,2,3,0]`, one vertex), labelled in `Perm (Fin 3)` by `![x⁻¹, x, y⁻¹, y]`. Its faces are:
  - `K = [0,2]`, the relator cell `pocketCell` with word `x⁻¹ y⁻¹`;
  - `Π = [1]`, the relator cell `petalCell` with word `x`;
  - `O = [3]`, the exterior face.
- `pinchedK : PocketFaceSet D 0 roseDiagram 0 1` has:
  - faces `{K}`, source `Π` and kept `K`;
  - sourceArc `[1]`, which reads backwards as `[0]`, and targetArc `[2]`;
  - boundary cycle `[0,2]`.

  `label_isLetter` and `pinchedK_closedWalk` are the hypotheses of `PocketPinchLabelledStatement`.
  `pinchedK_not_simple` says the cycle is not simple.
- `petalK` has faces `{Π}`, source `K` and kept `Π`. Its sourceArc is `[0]`, its sides and
  targetArc are empty, and its cycle is `[1]`. `petalK_simple` holds.
  `pinchedPocketPetal_conclusion` is the statement's conclusion at `pinchedK`, with
  `X' = roseDiagram` and the identity O-equivalence. `petalFaces_not_subset` says `{Π} ⊄ {K}`.
- The vertex split fails.
  - `corner_zero`: the corner after `0` is `Π`, a relator cell.
  - `corner_two`: the corner after `2` is the exterior face.
  - `not_mem_faces_corner_iff`: these are the only darts whose corner is outside `{K}`.
  - `isEmpty_input`: `IsEmpty (PinchSplit.Input roseDiagram)`, because every face is a relator
    cell or the exterior.
- The lake absorption does not apply.
  - `boundaryEdge`: every dart is a boundary edge of `{K}`.
  - `eq_outer_of_mem_component`: so the exterior piece is `{O}`.
  - `source_not_mem_component`: `Π` is not in it, which is the failed hypothesis of
    `OsinPocketLakeAbsorption`.
  - `source_mem_absorbed`: `Π` lies in the absorbed lake.
- `LakeRoseLabelledModel` / `lakeRoseLabelledModel` bundles these facts. The module runs
  `#audit_closed_axioms` on `pinchedK_closedWalk`, `petalK_simple`,
  `pinchedPocketPetal_conclusion`, `isEmpty_input` and `lakeRoseLabelledModel`, and
  `#audit_axioms` on the rest. It certifies no printed sentence.
- What it calibrates: at B, both routes' hypotheses fail, yet the statement holds there.
  - The routes are `PinchSplit.Input` and `OsinPocketLakeAbsorption`.
  - Its witness swaps source and kept, and its faces are not contained in `K`'s faces.
  - So a proof that covers a lake containing `Π` needs a step other than those two routes. This
    model does not show that no witness inside `{K}` exists in another O-equivalent diagram.
- Infrastructure: `nmprobe.sh` (l.43) refuses any line of `lanes/<lane>.files` that is not a
  `GroupApproximation/**/*.lean` path. The report line was removed from `lanes/audit-sec3.files`
  (backup `backup/audit-sec3/audit-sec3.files.pre-rose`), and the report is landed without a probe.

## Turn-condition survey (lead item, 2026-09-13 16:25)

The lead asked me to classify the pocket walk of each user of `PocketPinchStepStatement` /
`PocketPinchLabelledStatement`, and its producer, into one of four classes:
- (a) `K.boundary.FollowsBoundary`;
- (b) a `FirstTurn` chain on `c = K.boundary.cycle.reverse.map alpha` (hull-select `a29b02280`);
- both;
- neither.

The table went to hull-respell, with a copy to the lead. Base origin/main `840b774bd`. No Lean was
edited.

- (b) is outer-follows.
  - (b) implies that the reversed walk is noncrossing and that the outer cycle follows the
    boundary. Formal: `OsinPocketFirstTurnWalk` l.207 and l.247. The inner cycle
    `c.reverse.map alpha` is at l.334-340 and the outer cycle `c` at l.344-350.
  - Outer-follows implies (b) via `FirstTurn.of_boundaryWalk` l.153. On paper, not composed.
  - (a) is inner-follows.
- Users.
  - Neither:
    - `OsinPocketPieces`: l.497-515, with K at l.508 and `hpinch` at l.509; also l.521-535;
    - `OsinPocketCutResiduals` (l.45-64);
    - `OsinDescentResiduals` (l.40-66);
    - `OsinGreendlingerOpenResiduals` (l.52-68).

    Each gets K from `hfaces : SectionPocketFaceSetInput` (Pieces l.228-242), which gives only
    `K.ClosedWalk`.
  - `OsinPocketLakeLabelledModel` `pinchedK` (cycle `[0,2]` on `OsinPocketLakeModel.M`): (a) yes,
    (b) no.
    - (a): formal at map level, `lakeCycle_innerCycle_followsBoundary` (LakeModel l.158). At
      faces `{K}` it is a hand check.
    - (b) no: formal, `lake_not_firstTurn` (`OsinPocketFirstTurnWalkModel` l.105, `b8c0033c0`) on
      the same map, since `[3,1] = [0,2].reverse.map alpha` (l.98).
    - Its witness `petalK` (cycle `[1]`) is both, by hand: `FirstTurn [0] 0 0` holds with k = 3.
- Producers.
  - The planned producer is Blocker 1's first-turn route (rulings 16:00, sec2-sentences).
    - `firstTurnWalkPocketInputs` (FirstTurnWalk l.300) feeds `hw` and the outer-follows
      `hfollows` to `exists_kept_of_noncrossing_of_value` (KeptCellNoncrossing l.84-85).
    - `toPocketFaceSetOfNoncrossing_cycle` (SectionFaceSet l.330-333) sets
      `boundary.cycle = K.walk`.
    - So this route certifies (b) for the walk it produces. It is not composed on main.
    - `SectionPocketFaceSetInput` drops the condition, so carrying (b) to `hpinch` needs a
      respell of the Input, which is kh-ejz's statement.
  - No producer on main certifies (a) for a pocket walk.
    - The parity pieces (WalkChain, WalkColour, ColourNoncrossing) carry no turn condition.
    - `OsinPocketRegionNoncrossingWalk` l.53-130 takes outer-follows.
    - `exists_pinchStep_of_inside` (PinchCarry l.259-279) takes `StretchAvoids` turn conditions
      (l.262, l.264).
- Extra rows.
  - Configuration A `pinchedK` `[5,3,4,6]` (Lobe l.179).
    - (b) yes, formal: `pinch_isChain` l.51, `pinch_close` l.61, `pinch_reverse_map_alpha` l.71.
    - (a) no, formal: `pinchedK_not_followsBoundary` l.200.
  - dgo-geometric's `wrapK` (`OsinPocketWrapRose` l.333, cycle `[0,2]`).
    - (a) yes, formal: `wrapK_followsBoundary` l.377.
    - (b) no, by hand. With `c = [3,1]`: alpha 3 = 2 and sigma 2 = 3 ∈ c, so the first turn from
      3 is 3, not 1. The rotation fails the same way.
    - Probe `0913-163031-39703` reads `# PROBE GREEN`. Its record holds main's bytes of
      WrapMonogon (md5 `62af8739`) and WrapRose (`c3daeeca`), which landed as unverified at
      `6dfa779fe` / `87358b0ad`. Both are unwired.
- Consequence (hand composition of green pieces).
  - `PocketPinchWrapModel` (WrapRose l.403-416) bundles:
    - letters and `K.ClosedWalk`;
    - `K.boundary.FollowsBoundary` and `¬ Unpinched`;
    - no simple `K'` in any O-equivalent copy.
  - So `PocketPinchLabelledStatement` restricted to (a), or to (a) ∨ (b), is false at universes
    `0,0,0` if the conclusion is unchanged.
  - A Step Prop restricted the same way is false whenever its conclusion returns the condition,
    because it then iterates as in `pocketPinchLabelledStatement_of_step` (PinchStep l.72-89).
  - (b) excludes `wrapK` (by hand) and the rose `pinchedK` (formal), and admits configuration A
    (formal). No model on main refutes the (b)-restricted Prop.
  - The 16:00 ruling falls back to the disjunction when some consumer's walk does not come from a
    FirstTurn chain, and `wrapK` refutes that fallback. The recommendation sent is (b), with the
    Input respelled.
  - Under (b), the rose calibrates nothing about the step, because its `pinchedK` is outside the
    hypothesis. Configuration A is the calibration case.

### Revision after the lead's 16:35 additions (17:20)

The lead made three additions:
- a column (c), `IsNoncrossingClosedWalk`;
- sec2-sentences' finding that (b) fails for `exists_of_exteriorAt` walks;
- the instruction to classify under the provisional repair `0 < eps`.

Base origin/main at 17:18.

- Corrections to the table above.
  - "The planned producer certifies (b)" is wrong in general. sec2-sentences' obstruction
    (`d0c0519f6`, report item "Lead item 16:20") is a lake:
    - `x.rightSide` and `y.leftSide` pass through one vertex;
    - the first turn on `c = invDarts K.walk` reaches a dart of `c` before its target;
    - so (b) fails, and so does the outer-follows `hfollows`;
    - nothing in `exists_of_exteriorAt` excludes the touch.
  - "`wrapK` refutes (a) and (a) ∨ (b)" holds only at `eps = 0`.
    - w1-binder-7's `OsinPocketWrapRoseRescue.wrapRoseRescue` (`1b4736bcb`, l.118-125) gives the
      conclusion at every `eps ≥ 1`, with `rescueK = {R}` and first side `[5]`.
    - Probe `0913-170902-87292` reads `# PROBE GREEN` and holds main's bytes: `OsinPocketPinchPositive`
      md5 `833a6ff6`, `OsinPocketWrapRoseRescue` md5 `7e19c460`.
- Column (c) is automatic.
  - `PocketFaceSet.ClosedWalk.isNoncrossingClosedWalk` (hull-respell `24ff94312`,
    `OsinPocketClosedWalkNoncrossing` l.130-134) proves
    `IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle` from `K.ClosedWalk`, at every eps.
  - So restricting a pinch Prop to (c) changes nothing. The module docstring says the turning
    condition "does not choose how the walk pairs its darts".
  - The property the lead describes, a noncrossing chord diagram at each vertex, is a different
    predicate, (c'): the passages `(alpha x, next x)` at a vertex do not interleave in the rotation.
  - By hand, (a) ⇒ (c') and (b) ⇒ (c'), since a passage whose sector on one side is empty cannot be
    interleaved.
- Rows under `0 < eps`.
  - The classes depend only on the map and the cycle. Every model here has empty sides, so by hand
    it is a pocket face set at every eps.
  - Users: `OsinPocketPieces`, `OsinPocketCutResiduals`, `OsinDescentResiduals`,
    `OsinGreendlingerOpenResiduals`, and the repaired route
    `sectionPocketCutInput_of_residualsPos` / `osinSectionPocketCutSection_of_residualsPos`
    (`OsinPocketPinchPositive`, threshold `max eps0 1`). K still comes from
    `SectionPocketFaceSetInput`.
    - (a): not certified by any producer on main.
    - (b): not certified, and fails in the lake (sec2-sentences).
    - (c): yes, formal.
    - (c'): by hand, when the sides meet only at vertices (sec2-sentences' argument).
  - Rose `pinchedK`:
    - (a) yes, formal at map level;
    - (b) no, formal;
    - (c) yes, formal (`pinchedK_closedWalk` with `24ff94312`);
    - (c') yes, by hand: the passages `{1,2}` and `{3,0}` do not interleave.
  - Configuration A `pinchedK`:
    - (a) no, formal;
    - (b) yes, formal;
    - (c) yes, by composing `FirstTurnWalk.isNoncrossingClosedWalk_reverse` (l.220) with
      `pinch_isChain` and `pinch_close`;
    - (c') yes, since (b) implies it.
  - `wrapK`:
    - (a) yes, formal;
    - (b) no, by hand;
    - (c) yes, formal (`wrapK_closedWalk` with `24ff94312`);
    - (c') yes, by hand.
    - At `eps ≥ 1` its conclusion holds (`wrapRoseRescue`).
- Consequences.
  - At the interface, the users' walks carry only (c), which is free.
    - The planned producer gives no (b) in the lake, and no producer on main certifies (a).
    - So no producer on main supplies a restriction to (a), (b) or (a) ∨ (b).
  - The lake walk is (a) and not (b). A (b)-only step excludes it, and a disjunction covers it.
  - Under `0 < eps` I know of no model on main that refutes `PocketPinchLabelledPosStatement` or
    `PocketPinchStepPosStatement`, restricted or not.
  - sec2-sentences' `hfollows` is `(hw.outerCycle _).FollowsBoundary`, which is the (b) side. In the
    lake, (a) holds (`lakeCycle_innerCycle_followsBoundary`).
  - The candidate the producer side can plausibly certify is (c'), sec2-sentences' option (iv). By
    hand it contains both (a) and (b).

## Open (owned by other lanes)

- `b6d1590be7ab` (L1145, partial, ghw-charp2): the GHW wall, reported to the lead.
  `GHW.ghwFinitelyGeneratedCharP` (`Kazhdan/GHWCharPClosed`) is now on main and root-reachable, but
  the row is still partial in `metadata/nm-census-rows/ghw-charp2.tsv`.
- `c149d33e8f7e` (L1145, partial, jacobson): `manuscriptSentence_twoResultsComplementary` is in
  `JacobsonComplementarySentence.lean`, which the root does not reach. ghw-charp2 queued it for
  wiring at `42d443298`.
- `dcf6fa4be4de` (L1298) and `7916c8696def` (L1307), partial, leavitt-units: they name
  `LeavittMFQuotientUnitsGL`, which the root does not reach. leavitt-units queued it for wiring at
  `4f629158e`.
- `3009704fef89` (L1145) and `a4b5b1a0504a` (L1008) moved from formalized to partial at the census
  merge, so the regenerated gate no longer audits them.
- Wiring: `RingCompressionCellGeneral`, then `Audit.Sec3`. Until the carrier is wired, the census
  merge grades rows `718cc7b04afd`, `c0383f82a141`, `d1142160bf17` and `83ed5eb3b38c` partial.
  - Probe `0913-040726-62527` ran at base `840e6a1d8`. Up to origin/main `39dd43b39`, the gate's
    import closure has 1033 modules, and only the two probed files changed, at the probed bytes.
    So that probe stands for one at the current base.
  - The root already imports `Algebra.PreusserSandwichExchange` and
    `NonMFSentences.AmenableTraceSentencesB`, so neither becomes root-reachable only through a
    gate. The only module the gates newly make reachable is `RingCompressionCellGeneral`.
