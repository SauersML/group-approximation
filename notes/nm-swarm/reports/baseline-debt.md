# baseline-debt lane report

Lane `baseline-debt`, roster section `## baseline-debt`. The census findings are in
`metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt`. Line numbers below point into that file
at origin/main 8f4475102. Census rows are in `metadata/nm-census-rows/baseline-debt.tsv`.

## Landed

- `95e6d09ca`: three new modules, landed unverified. The only change since is a one-name
  fix in `StrongConvergenceMFSubsingleton`.
- `296386753`: the four modules in the table, from probe 0913-021321-7359.
  - The probe reported `PROBE GREEN` and COMPILED all four overlay files.
  - `StrongConvergenceMFSubsingleton` was rebuilt. The other three were replayed with the
    same input hash, after being BUILT in probe 0913-020324-57087.
  - The `#audit_axioms` and `#audit_closed_axioms` lines show only `propext`,
    `Classical.choice` and `Quot.sound`.
  - The three new modules are queued for wiring.
- `bf625daf4`: this report and the census rows.
- `72599dad7`, probe 0913-025420-71482: the stale docstrings that audit-sec5 found
  in `RegularNonMFAlgebra` and `TorsionFreePrintedSentences`. No statement changed.
  - The printed corollary and proof are quoted as they now read (tex 1718-1736). The
    not-MF clause cites `prop:mf-residual-calculus`, not an embedding into the corona's
    unitary group.
  - "No vocabulary for hyperbolically embedded" is replaced, in four places, by the closed
    `exists_isNonDegenerate_isHypEmbedded` (`OsinTheorem12NonDegenerate`, Osin 1.2,
    `(AH₁) ⇒ (AH₄)`).
  - `DGOTheorem235Printed` and `GerasimovaOsinTheorem11Printed` are recorded as proved:
    `dgoTheorem235Printed` and `gerasimovaOsinTheorem11Printed`. Both carry
    `#audit_closed_axioms` and are imported by the root.
- `dd0412114`, probe 0913-034738-16893: `GGT/HullLemma35Printed.lean` (new, definitions
  only), the statements of Hull Lemma 3.5 and of `{G₁, G₂} ↪h G₁ ∗ G₂`.
- `87762b46c`, probe 0913-051219-87168 (both modules BUILT): `GGT/HullLemma35FreeFactors.lean`
  (new) proves `printedFreeFactorsHypEmbedded`. The module doc of `HullLemma35Printed` now
  records the proof. Queued for wiring.
- `72a023f67`: this report, after the free-factor proof.
- `be6e71f04`: `GGT/HullLemma35Transitive.lean` and `GGT/HullLemma35LocalFinite.lean` (both
  new), the witness structure of Hull Lemma 3.5 and its local finiteness.
  - Probe 0913-081320-10853 was `PROBE GREEN` and BUILT `HullLemma35LocalFinite`.
  - `HullLemma35Transitive` was BUILT in 0913-080412-2056 and replayed with the same source.
  - `#audit_axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.
  - Both modules are queued for wiring.
- Hyperbolicity chain for Hull Lemma 3.5, all new modules, each probed green (BUILT, no
  warnings, `#audit_axioms` within the three axioms) and queued for wiring:
  - `5acca195c`: `GGT/HullLemma35Expansion.lean` (guessed paths, step and short-path bounds)
    and `GGT/HullLemma35Corner.lean` (the corner walk);
  - `28fbaaffe`, probe 0913-093041-78609: `GGT/HullLemma35Sides.lean` (side points,
    `LetterNear`, side hypotheses at both corners);
  - `6dd556d61`: `GGT/HullLemma35Thin.lean` (`thin`, the thin-triangle condition given
    `LetterNear`);
  - `7401027ce`, probe 0913-094811-36793: `GGT/HullLemma35PieceGeometry.lean` (quadrilateral
    and hexagon bounds, `nearBetween_quad`, `nearBetween_hexagon`);
  - `1369b2bed`, probe 0913-101453-98311: `GGT/HullLemma35PieceWords.lean` (`transEx`, the
    expansion of member letters into shortest words of `E i`; `properRelGenSet`; bounded
    expansions of relative balls);
  - `520f03021`, probe 0913-104731-79425: `GGT/HullLemma35PieceSides.lean` (coset
    coordinates, connector distances in `Γ(H i, E i)`, component letters as geodesic segments
    of the coset points, `exists_near_of_nearBetween`);
  - `0efcdd55c`, probe 0913-114118-23523: `GGT/HullLemma35Letter.lean`
    (`letterNear_properRelGenSet`, the quadrilateral and hexagon cases).
- `b5f91627e`, probe 0913-123731-5219 (both modules BUILT): `GGT/HullLemma35Closed.lean` (new)
  proves `printedHullLemma35 : PrintedHullLemma35`. The module doc of `HullLemma35Printed`
  now records the proof. `#audit_closed_axioms` shows only `propext`, `Classical.choice` and
  `Quot.sound`. Queued for wiring.
- `a719c860b`: the census row for the DGO 2.35 half moved from LINE:1725 to LINE:1728 and is
  graded formalized.
- `7976a7ca7`, probe 0913-132138-96143 (BUILT): `GGT/DGOProposition435PrintedCounterexample.lean`
  (new) proves `RelHyp.not_dgoProposition435PrintedStatement`, per the team lead's ruling. It
  refutes the Lean spelling, not DGO's printed Proposition 4.35. Queued for wiring.
- `348fc1af7`: the cite-ejz LINE:1155 re-grade and this report, after the C6′ assignment.

| module | declarations |
|---|---|
| `Manuscript/NonMFSentences/FullDefectPairLeavitt.lean` (new) | `fullDefectPair_aryLeavittAlgebra`, `fullDefectPair_aryLeavittAlgebra_zmodTwo` |
| `Sofic/StrongConvergenceMFSubsingleton.lean` (new) | `isStronglyOperatorMF_of_subsingleton`, `isStronglyOperatorMF_unit` |
| `Manuscript/NonMF/NaiveFreeProductPropertyOfAcylindricallyHyperbolic.lean` (new) | `naiveFreeProductProperty_of_isAcylindricallyHyperbolic`, `powersAveragingEstimate_of_isAcylindricallyHyperbolic` |
| `Manuscript/NonMF/TorsionFreePrintedSentences.lean` (edited) | `PrintedTheoremQuotientTrivial`, `manuscriptSentence_theoremQuotientTrivial : PrintedTheoremQuotientTrivial` |
| `GGT/HullLemma35Printed.lean` (new) | `IsHypEmbeddedFamily`, `PrintedHullLemma35`, `PrintedFreeFactorsHypEmbedded` |
| `GGT/HullLemma35FreeFactors.lean` (new) | `printedFreeFactorsHypEmbedded : PrintedFreeFactorsHypEmbedded`, `FreeFactorsHypEmbedded.factorsRelGenSet`, `FreeFactorsHypEmbedded.relBall_finite`, `FreeFactorsHypEmbedded.isFourPointHyperbolic_alphabet` |
| `GGT/HullLemma35Transitive.lean` (new) | `HullLemma35.transitiveRelGenSet`, `isSymmetricGeneratingSet_transitive`, `transitive_alphabet_subset` |
| `GGT/HullLemma35LocalFinite.lean` (new) | `HullLemma35.relBall_finite_transitive`, `exists_enlargedWord`, `relBall_subset_image` |
| `GGT/HullLemma35Closed.lean` (new) | `printedHullLemma35 : PrintedHullLemma35`, `HullLemma35.isHyperbolicallyEmbedded_transitiveRelGenSet`, `HullLemma35.exists_guessingData_transitive` |
| `GGT/DGOProposition435PrintedCounterexample.lean` (new) | `RelHyp.not_dgoProposition435PrintedStatement : ¬ DGOProposition435PrintedStatement.{u, v, w}`, `fiveRelGenSet_isHyperbolicallyEmbedded`, `pairRelGenSet_isHyperbolicallyEmbedded` |

## Findings closed

The census merge at 63f147d7b removed all five findings as stale ("matches no finding").
Baseline lines 78, 97, 171, 238 and 298 are now `# REMOVED` comments.

- **(a) open-predicate `FullDefectCornerRemark.manuscriptSentence_cornerPassesUp`**
  (baseline 238, tex 1008).
  - The premise `FullDefectPair (Corner R p hp)` is the printed hypothesis of the sentence:
    "the ring pRp, with unit p, satisfies the hypothesis".
  - `FullDefectPair` has an honest producer. At `L_k(1,d)` with `d ≥ 2`, take `s = s₀` and
    `t = t₀`; then `t₁(1 - s₀t₀)s₁ = 1`. It is closed at `L_{𝔽₂}(1,2)`.
- **(b) inlined-statement `TorsionFreePrintedSentences.manuscriptSentence_theoremQuotientTrivial`**
  (baseline 171, tex 1711-1716).
  - The theorem is now the closed endpoint `PrintedTheoremQuotientTrivial`, with no
    binders, proved from `manuscriptSentence_theoremHomsTrivial`.
- **(c) open-predicate `ReducedGroupCStarTrace.powersAveragingEstimate_of_naiveFreeProductProperty`**
  (baseline 298, tex 1725).
  - `NaiveFreeProductProperty G` is produced at countable acylindrically hyperbolic `G`
    with `HasTrivialFiniteRadical G`, from the closed `naiveFreeProductAtAcylindricallyHyperbolic`.
  - The classifier's least fixpoint admits this producer: its corpus premises have closed
    producers, `instIsAcylindricallyHyperbolicFreeGroupFinTwo` and
    `hasTrivialFiniteRadical_of_torsionFree` from `isPowerTorsionFree_multiplicative_int`.
    The census merge confirms it.
- **(d) carrier-data `IsStronglyOperatorMF` (baseline 78) and open-predicate
  `IsStronglyOperatorMF.isOperatorMF` (baseline 97)**, tex 99 (printed 102-105).
  - Verified: `not_isStronglyOperatorMF_of_not_isOperatorMF` is the printed contrapositive.
  - The carrier has an honest producer: a trivial group is strongly MF, closed at `Unit`.

## (e) carrier lines and (f) remaining findings: classification

Every active finding names its owner in its baseline note. None is an unowned non-wall
citation.

- Not walls, already owned:
  - 341, inlined-statement `LeavittMFQuotientBothInclusions.elementary_le_commutator_of_trivial`:
    owner leavitt-units. The premise is `thm:full-defect-ring` at `L_k(1,d)`, proved inside
    the sibling carrier.
  - 362, buried-conditional `HullTheorem312Lemma58.normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded`:
    owner cite-hull. The premise is Hull Lemma 5.8's printed hypothesis, not a citation.
- Walls only:
  - 381 `HullSC.hullCommonQuotientPrinted_of_oneStep`, from the Theorem 7.1 leaves: owners
    hull-respell, hull-bridge, sec5-sentences.
  - 393 `TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_closedCitations`, from
    FFF S2 through `KotowskiOllivierStatement` and `FinitelyPresentedInfiniteSimpleStatement`:
    owners simple-group, kh-hyperbolic, kh-torsion.
  - Every other active line is one of three kinds:
    - an `_of_leastAreaLeaves`, `_of_hullLeaves(_closedGO)`, `_of_fourLeaves`,
      `_of_leastAreaInputs`, `_of_leastAreaKOLeaves`, `_of_leastAreaZipFold` or
      `kotowskiOllivier_of_leaves` wrapper, with its buried-conditional twin;
    - a carrier-data `Printed*` line produced only through those wrappers: 267, 321, 322,
      350-353, 363, 366, 377, 388, 391, 392;
    - the conditional-data 378 `fournierFacioParagraph_of_literatureInputs`.
    nm-endpoints owns the wrappers.

## Residual statements (exact)

1. `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`
2. `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}`
3. `TheoremC.KotowskiOllivierStatement`
4. `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`

These walls are owned by other lanes: hull-*, kh-* / ko-closed, and simple-group. Wall 4 is
closed by `finitelyPresentedInfiniteSimple_closed` (47b31bef8, simple-group).

This lane's own item `GGT.PrintedHullLemma35.{u}` is closed (below).

## Hull Lemma 3.5

Ruling of 09-13 08:30: this lane owns Hull Lemma 3.5, including the printed form. cite-hull
stands off it.

- Source checked against arXiv:1308.4345v2 (`pdftotext -layout`).
  - Lemma 3.5 is on p. 12 of §3. Hull prints it without a proof, as a "simplification of
    [DGO, Proposition 4.35]".
  - Definition 3.1 defines `{H_λ} ↪h G` as `↪h (G, X)` for some `X ⊆ G`.
  - The proof of Corollary 7.4 (§7) says "Since `{G₁, G₂} ↪h F`, Lemma 3.5 gives that
    `{⟨f₁⟩, ⟨f₂⟩, ⟨h₁⟩, ⟨h₂⟩} ↪h F`".
  - Hull's Lemma 5.9 also "follows from Lemma 5.8 and Lemma 3.5".
- Statements, `GGT/HullLemma35Printed.lean` (`dd0412114`):
  - `IsHypEmbeddedFamily G H := ∃ D : RelGenSet G Λ, D.fam = H ∧ D.IsHyperbolicallyEmbedded`;
  - `PrintedHullLemma35.{u}`: all `n`, `H : Fin n → Subgroup G`, `m`, and
    `K : ∀ i, Fin (m i) → Subgroup (H i)`, with the family indexed by `Σ i, Fin (m i)`;
  - `PrintedFreeFactorsHypEmbedded.{u}`: `![inl.range, inr.range]` in
    `Monoid.Coprod G₁ G₂`, for all groups.
- **`PrintedFreeFactorsHypEmbedded`: closed.** `printedFreeFactorsHypEmbedded` in
  `GGT/HullLemma35FreeFactors.lean` (`87762b46c`) carries `#audit_closed_axioms`. The
  witness is `X = ∅`.
  - Local finiteness: every relative ball is `{1}`. The invariant "the partial product is
    `1` or its reduced word begins in the other factor" uses `RelHyp.headIdx_mul_of`.
  - Hyperbolicity: `isFourPointHyperbolic_unionCarrier` at the full factor alphabets
    (`δ = 1`), carried along `coprodIBoolEquiv` in every universe.
- **`PrintedHullLemma35`: closed** by `printedHullLemma35` in `GGT/HullLemma35Closed.lean`
  (`b5f91627e`, probe 0913-123731-5219), with `#audit_closed_axioms`.
  - The witness is `transitiveRelGenSet D E` (`be6e71f04`). Its base is `RelHyp.properBase D`
    together with the images of the bases of the `E i`, and its members are the `K_{ij}`.
    The letters of `D.base` that lie in some `H i` are dropped. Keeping them fails, because
    the inverse of such a letter may be a letter only of `H i`. Hull's base is existential,
    so dropping them costs nothing.
  - Local finiteness: `relBall_finite_transitive`. A path of length at most `n` is read
    through `H i`. Every excursion out of `H i`, and every letter of another member, becomes
    one letter of the finite set `excursionLetters D i n ⊆ D.relBall i n`. The bound is the
    Corollary 4.27 local half, `RelHyp.relBall_finite_adjoinBase'`.
  - Hyperbolicity: `isHyperbolicallyEmbedded_transitiveRelGenSet`. The route is the guessing
    geodesics criterion (`OsinEnlargement.exists_isFourPointHyperbolic_of_guessingData`)
    along a geodesic word of `properRelGenSet D`, with each component letter expanded into a
    shortest word of `E i` (`transEx D E`). `exists_guessingData_transitive` builds the
    `GuessingData`. This generalizes the `Uncone` chain from cyclic members to hyperbolic
    replacement graphs.
    - Step and short-path conditions: `wordDist_guessPath_succ`, `guessPath_short` and
      `length_transEx_le_of_wordNorm_le_one`.
    - Thin-triangle condition: `thin`, given `LetterNear (properRelGenSet D) (transEx D E) S T`,
      the bound on the expansion of a letter whose coset another side meets.
    - `LetterNear`: `letterNear_properRelGenSet`. The triangle connectors
      (`Uncone.TriangleConnectors`) close a quadrilateral (one other side meets the coset) or
      a hexagon (both do) in `Γ(H i, E i)`, bounded by `nearBetween_quad` /
      `nearBetween_hexagon`. `HullLemma35PieceSides` gives the coset coordinates, the
      connector sides and the transfer back to the transitive alphabet.
    - Constants: `δ` and the hexagon bound `C` of `properRelGenSet D`
      (`sixBound_one_of_fourPointHyperbolic`), one `δE` for all `E i` (the index `Fin n` is
      finite), and the expansion bounds of `exists_pieceWord_length_le`.
- **Finding: `RelHyp.DGOProposition435PrintedStatement` is false as formalized.** Proved by
  `RelHyp.not_dgoProposition435PrintedStatement : ¬ DGOProposition435PrintedStatement.{u, v, w}`
  in `GGT/DGOProposition435PrintedCounterexample.lean` (probe 0913-132138-96143, BUILT). `#audit_axioms`
  shows only `propext`, `Classical.choice` and `Quot.sound`.
  - It refutes the Lean spelling, not DGO's printed Proposition 4.35. When every `M λ` is
    empty, the conclusion has no members, so the forced base would have to be closed under
    inversion on its own. It is not, so no `RelGenSet` has it.
  - Counterexample: `G = ULift (Multiplicative (ZMod 5))` with generator `t`, `D.base = {t²}`,
    `fam = ⊤`, `M = PEmpty`, `E.base = {t, t⁻¹}`. The forced base `{t², t, t⁻¹}` does not
    contain `t⁻²`.
  - The `h435` consumers in `GGT/DGOProposition435Printed.lean` are vacuous, so none of them
    is a carrier: `isRelativelyHyperbolic_original_of_jointPreservation` (line 315),
    `isRelativelyHyperbolic_original_of_jointPreservation_of_cyclic` (line 404) and
    `canonicalQuotientFamilyPreservation_of_jointPreservation` (line 561). This lane's route
    does not use that statement.
  - Per the 09-13 ruling, `GGT/DGOProposition435Printed.lean` stays unedited. No census row
    names it, so nothing needs re-grading.

## Census debt outside W1 (merge 17)

Assigned by the team lead at about 13:10 on 09-13. The source is
`metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt` at census merge 17 (`d0aba6104`), which is
still the origin copy. The 146 active findings are grouped below by the residual each note
names. Only text scans were run.

- `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (W1): 108 findings.
  - 85 say "the residual is hgreendlinger".
  - 23 say "over the least-area leaves". Their other leaf, hbridge, is closed (`18682110d`).
  - 14 of them also carry the hKO classifier false red, which systolic-counts' verifier fix
    handles.
- Lemma 9.4 pieces on nm-endpoints' leaf list (`e3e3dda23`, W1): 30 findings.
  - Planar pieces and `OsinLemma94PlanarRunInput`: 9.
  - Polygon realization: 11.
  - Chain respelling: 8.
  - Side budget: 2.
  - 19 of these notes still list five pieces as open that have closed since: CornerInsertionInput,
    PendantPathRemovalInput, CellArcsInput, BoundaryArcsInput and QuasiGeodesicRespellInput.
- No residual Prop: 8 findings, all accepted lines.
  - Not a conditional, 6.
    - Closed: `HullSC.quotientPeripheralLetterPullbackStatement_holds` and
      `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`.
    - Lemmas about any cut lift or G-face merge: `HullSC.cutLiftOutcome`,
      `HullSC.CutLift.toCutMove`, `Surgery.GFaceMerge.facePerm_keep_of_ne` and
      `Surgery.GFaceMerge.sigma_keep_eq_self`.
  - Definition premise, 1: `HullTheorem312Lemma58.normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded`.
    The premise is DGO Definition 4.25, inside Hull Lemma 5.8's printed hypothesis.
  - Inlined premise proved in a sibling carrier, 1:
    `LeavittMFQuotientBothInclusions.elementary_le_commutator_of_trivial` (`thm:full-defect-ring`).

No active finding outside W1 names a residual Prop. Of the 17 partial union rows on origin, 14
are over hgreendlinger. Each of the other three is partial through one stale lane row:

- LINE:1725 `92115dd7edef`: this lane's old row, moved to LINE:1728 at `a719c860b`. It should
  clear at the next merge.
- LINE:1629 `a9dd4b90e479` (Hull Theorem 3.12).
  - sec5-sentences' row 5 still calls the hard direction of Osin Theorem 1.1 open.
  - That direction is on origin as `OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet`
    (`GGT/OsinLimitSetSpelling.lean:47`), a ∀-statement with no binders, with `#audit_axioms`.
  - cite-hull's two rows grade the sentence formalized over `printedHullGeneratingSetLimitSet`
    and `printedHullTheorem312LimitSet` (`#audit_closed_axioms`, root-imported).
- LINE:1145 `3009704fef89` (EJZ Theorem 1.1).
  - cite-ejz's row 2 (key LINE:1155) was partial: "First half only; the jacobson row carries
    the whole sentence".
  - jacobson's row 26 grades the sentence formalized over
    `manuscriptSentence_threePlusOneGeneral` (`#audit_closed_axioms`, root-imported), which
    packages both halves.
  - No lane of this swarm owned `cite-ejz.tsv`. Per the lead's ruling, this lane re-graded the
    row formalized at `348fc1af7`.

Six more partial lane rows, at LINE:1636, 1675 and 1679, name no Greendlinger leaf. Each
carries one piece of a longer sentence, and those union rows stay partial through
hgreendlinger, so re-grading these rows flips nothing now.

- Two rows give a reason that is now stale.
  - fff-quotient, LINE:1636, calls finite presentation "the one hypothesis, owned by
    simple-group". It is closed as `HydeLodha.finitelyPresentedInfiniteSimple_closed`
    (`GroupTheory/HydeLodha/FinitelyPresentedInfiniteSimpleClosed.lean:49`,
    `#audit_closed_axioms`). The row also asks the lead to confirm its tex line. simple-group
    and hl-lemma46 key the same Hyde–Lodha witness at LINE:1679.
  - kh-torsion, LINE:1675, says the sentence "stays partial until hfold (MirrorFoldStatement)
    closes". Both fold cases are proved as `Systolic.mirrorFoldDistinct` and
    `Systolic.mirrorFoldPinched` (`#audit_axioms`). hKO is closed as
    `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed` (`#audit_closed_axioms`).
- Four rows are accurate:
  - ko-closed, LINE:1675 (hKO);
  - kh-ejz, LINE:1675 (its own route over hconj and hhyp, CCKW 3.1);
  - hl-lemma46, LINE:1679 (the Lemma 4.6 dynamics);
  - simple-group, LINE:1679 (hW). This sentence also needs the hull-* and kh-* leaves.

`merge_rows.py` keeps a union row partial while any lane row is partial. So once hgreendlinger
closes, these piece rows still hold their union rows partial unless they are re-graded or
census overrides them. cite-ejz's row did the same to LINE:1145 until its re-grade at
`348fc1af7`.

## C6′: `OsinTwoGonHoldsSectionStatement` (Lemma 9.3, hcount)

Assigned by the team lead on 09-13, split with debt-conditional.
`OsinTwoGonHoldsSectionStatement` (`Estimating/OsinAppendixEulerSection.lean:49`) is the last
open binder of `osinPhiPrimeCountSection_of_pieces`, since C4 is closed
(`osinCornerTwoGonSection`, `0c42391c2`). `TwoGonHoldsInput` does not use the parameters, so a
producer of it for all `D`, `λ`, `c`, `ε` and `W` gives the section statement with `eps0 = 0`
and `rho0 = 1`.

- debt-conditional's plan (its report of 13:50):
  - module 1 `OsinAppendixEulerTwoGonLabels` (`81cb719d3`, green): the cell `i`, the section
    `j` and the regions `a ≠ b`;
  - module 2 `OsinAppendixEulerTwoGonFaceClass` (`ee96efa9d`, green): the face-class tools;
  - module 3: given `outerFace ∉ sideFaces` and `(cell i).face ∉ sideFaces` for the pocket
    walk, the pocket holds no relator cell and meets no other region;
  - module 4: `PocketRegion.ofSimpleClosedWalk` on `S.diagram`, then `EmptyTwoGonInput`, which
    is proved (`emptyTwoGonInput_holds`, `2aa17abb0`).
- Offered to debt-conditional: the face-class side link, or the closure from a relator-free
  pocket. This lane writes only new modules and waits for debt-conditional's pick.
- Checked against the definitions on origin:
  - `outerDarts` is the reversed outer boundary under `alpha` (`Estimating/Embedded.lean:79`).
    So walk darts face into the pocket, and for a noncrossing walk
    `sideFaces S.diagram.toCombMap K.walk` is the pocket side. `PocketFaceSet.ofBoundaryCycle`
    proves `outerFace ∉ faces` the same way.
  - Without noncrossing, `sideFaces` leaks.
    - (a) If the target arc holds both darts of a spur, one walk dart lies on the outer face.
    - (b) If a gap edge has cell `i` on both sides, a walk dart lies on cell `i`.
    - (c) is expected to leak through the interior of `a` or `b`, but this is not checked
      against the side orientation.
    So module 3's two inputs fail in the copy configurations, and those cases need the copy.
  - The 13:40 ruling's route for module 4 (roster `0da58be4b`) does not compose as stated. That
    route is kh-ejz's copy face set, then `PocketPinchLabelledStatement`, `ofSimpleClosedWalk`
    and EmptyTwoGon.
    - `SectionPocketFaceSetInput` (`Estimating/OsinPocketPieces.lean:228`) returns a
      `PocketFaceSet` on a copy `X'`. It carries a `kept` relator cell and has no link to `a`,
      `b` or `S.diagram`.
    - `EmptyTwoGonInput` needs a `PocketRegion S.diagram` that contains `a.1` and `b.1` and no
      relator cell.
    - Sent to the team lead with a question: does dgo-analytic's zero-cell merge on the copy
      (Q2) also cover the two-gon pocket?
- A copy route for module 4, checked on origin:
  - The conclusion of `TwoGonHoldsInput` is `False`, so it is O-invariant and needs no
    transport.
  - The premises do not transport.
    - `OEquivalentDiscDiagram` (`RelativeGreendlinger.lean:123`) has only `boundaryWord_eq`,
      `cellIndex` and `cellWord_eq`, with no darts or faces.
    - `OuterSpurThickeningStatement` (`SurgeryOuterSpurThickening.lean:51`) keeps the family
      bijection, the weight, the target profiles and the source indices. It does not carry
      `NoLoops`, `NoMultipleEdges`, the two-gon `f` of `phiMapO`, `¬GapAtOHoldsCorner` or
      `¬HoldsCellO`.
    - So a copy route re-derives the pocket's emptiness on the copy, as sec2-sentences does for
      the kept cell (`3fce53dd1`).
- The simple-walk case of module 4 is on origin already:
  `GloballyDistinguishedSectionFamily.exists_kept_of_simple`
  (`Estimating/OsinPocketKeptCell.lean:163`, sec2-sentences `492057fb6`, probe
  0913-140023-67387 GREEN, unwired).
  - Its binders are the output of `PocketWalk.exists_of_exteriorAt`
    (`OsinPocketSectionFaceSet.lean:427`) on module 1's labels: `x ≠ y` exterior to cell `i` and
    targeting section `j`, `K`, `hgap`, `hstart` and `hend`. It also takes
    `hw : IsSimpleClosedWalk S.diagram.toCombMap K.walk` and `havoid`, which ranges over all of
    `S.family`.
  - It returns a relator cell on `sideFaces S.diagram.toCombMap K.walk`, through
    `false_of_disc_pair_singleton`, with no `EmptyTwoGonInput` binder.
  - So the simple case is module 3 plus `exists_kept_of_simple`, and the residual is the
    non-simple walk (a pinch or a leak).
  - Module 3's two inputs for a simple walk are on origin as well:
    `PocketFaceSet.outerFace_not_mem_sideFaces_of_mem_outerDarts`
    (`OsinPocketSectionFaceSet.lean:99`) and `PocketFaceSet.cell_face_not_mem_sideFaces`, the
    theorem after it. So the simple-case glue is only `exists_twoGonLabels`, then
    `exists_of_exteriorAt`, then `exists_kept_of_simple`.
  - Sent to debt-conditional with an offer: the simple-case glue, in a new module of this lane.
- The premise list for the thickened copy `S'`, sent to hs-vanishes (rulings-1425 asks for it;
  hs-vanishes transports the C6′ premises):
  - `S'` from `OuterSpurThickeningStatement` (`SurgeryOuterSpurThickening.lean:51`) lies over
    the same `Delta` and `cuts`, so `Delta.LeastArea` needs no transport.
  - All 13 binders of `TwoGonHoldsInput` are the full list. Two of them fail to transport with
    the landed statement:
    - `S'.NoLoops` and `S'.NoMultipleEdges` read `target = some k`;
    - `SameTargetProfile` (`GFaceQuadrilateralRegion.lean:44`) keeps `target = none ↔`, the
      target start and length and the source length, and the statement adds `source.val`, so
      the target cell index is not kept;
    - the two-gon, corner and cell premises are faces of `phiMapO`, which is built from darts.
  - The narrower list, recommended. Module 1's labels transport along `e` with the landed
    statement: `exteriorAt` reads `target = none` and the source index, and
    `TargetsSectionIndex` reads `target = none`, start and length. On `S'` there remain `hno`
    (no relator cell on `sideFaces S'.diagram.toCombMap K'.walk`), `havoid` and `hw` for the walk
    of `exists_of_exteriorAt`, and `exists_kept_of_simple` gives False. None of the three follows
    from the landed statement. For a pinched walk, `emptyTwoGonInput_holds` takes a
    `PocketRegion` instead of `hw`.
  - No face map is needed in the statement: the conclusion is False and names neither `f` nor
    `S`.
  - Hand model, not tested in Lean: no outer spur does not make `K'.walk` simple. A vertex of
    cell `i` on `∂Δ` inside the gap pinches the walk without a spur.
- No C6′ Lean from this lane yet.

## Next

- Wiring: the root on origin/main imports every module of `296386753`, `dd0412114`,
  `87762b46c`, `be6e71f04`, `5acca195c`, `28fbaaffe`, `6dd556d61`, `7401027ce`, `1369b2bed`
  and `520f03021`. `HullLemma35Letter` (`0efcdd55c`), `HullLemma35Closed` (`b5f91627e`) and
  `DGOProposition435PrintedCounterexample` are queued.
- The team lead accepted (a) through (d) as closed; census registers them at its re-baseline.
- The census row for the DGO 2.35 half moved from LINE:1725 to LINE:1728, the sentence it
  describes, and is graded formalized (request relayed by dgo-geometric). Its `partial` grade
  at 1725 had pulled union row `92115dd7edef` partial.
- Census row LINE:1682 (partial) records `printedHullLemma35`. Hull Corollary 7.4 and Lemma 5.9
  use Lemma 3.5. They belong to other lanes.
- Census debt outside W1: no Prop group is left to formalize. The roster records the lead's
  ruling (`0da58be4b`, `ROSTER-0913.md:828`): this lane re-grades the cite-ejz LINE:1145 row,
  and sec5-sentences re-grades LINE:1629.
  - Landed at `348fc1af7`. cite-ejz row 2 (key LINE:1155, union row `3009704fef89`) now also
    lists jacobson's whole-sentence carrier, `JacobsonPresented.PrintedThreePlusOneGeneral` and
    `manuscriptSentence_threePlusOneGeneral`, and is graded formalized.
  - Checked on origin: the carrier has `#audit_closed_axioms`
    (`JacobsonThreePlusOnePresented.lean:98`), the root imports the module
    (`GroupApproximation.lean:4962`), and tex 1155-1157 is the sentence of jacobson's row 26.
- C6′: waiting on debt-conditional's pick, either the simple-case glue offered above or another
  piece, and then writing it in a new module of this lane. Also waiting on the lead's answer on
  the copy zero-cell merge for the two-gon pocket.
