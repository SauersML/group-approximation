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
  - cite-ejz's row 2 (key LINE:1155) is partial: "First half only; the jacobson row carries
    the whole sentence".
  - jacobson's row 26 grades the sentence formalized over
    `manuscriptSentence_threePlusOneGeneral` (`#audit_closed_axioms`, root-imported), which
    packages both halves.
  - No lane of this swarm owns `cite-ejz.tsv`.

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
- Census debt outside W1: no Prop group is left to formalize. The pick sent to the team lead
  is the two stale re-grades: sec5-sentences' LINE:1629 row, and the ownerless cite-ejz
  LINE:1155 row. This lane edits the cite-ejz row only on the lead's word, and otherwise waits
  for a W1 leaf.
