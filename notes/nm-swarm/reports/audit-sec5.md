# audit-sec5 lane report

Lane `audit-sec5` has two parts.

- **Part 1** audits tex 1621–2022 of `non_mf_groups_exist.tex`: `sec:torsion-free`, Origin and
  authorship, and Acknowledgments.
- **Part 2** is the lead's 09-13 truth and fidelity audit of the open W1 and W2 leaf Props.

## Landed

- **`8a7de88a6`** (probe `0913-015553-23837` GREEN, BUILT both modules; both are now root-wired):
  - `GroupApproximation/Manuscript/NonMF/Audit/Sec5.lean`, the permanent gate. It runs
    `#audit_closed_axioms` on the named-Prop endpoints and `#audit_axioms` on every other
    carrier the census names for this range, together with the route theorems they rest on.
  - `GroupApproximation/Manuscript/NonMF/TorsionFreeDefectNormalClosure.lean`, the carrier for
    the clause that row `d29816e1de56` was missing (defect 1 below).
- **`bf377dbdc`**: this report, first version, and the `d29816e1de56` row.
- **`b0a084d16`**: the `f2bf6328169e` row.
  - `TorsionFreeAlgebraSentencesClosed` probed GREEN (`0913-021620-22844`).
  - It was queued at `3f71a3a50`, its last change, and is now root-wired.
- **`3f6eaff76`**: `GroupApproximation/GGT/VanKampen/RegionShellingSpurCounterexample.lean`
  (probe `0913-035624-34720` GREEN, BUILT), the refutation in part 2.

# Part 1: tex 1621–2022

## The rows in range

There are 53 census rows: 3 structural, 1 definition, 15 formalized, 13 partial, 19 provenance and
2 attribution.

1. **Reachability.** Every declaration named by the 16 formalized and definition rows exists on
   origin/main (9f819ad8c), in a module the root reaches. The modules are
   `TorsionFreePrintedSentences`, `PrintedDefectParagraph`, `SimpleInDefect`,
   `GGT.OsinLemma71Printed`, `OsinTheorem12NonDegenerate` and `AcylindricallyHyperbolic`.
2. **Gate.** `Audit/Sec5.lean` audits all of them.
3. **Reading against the print.** Each carrier states the printed sentence at the printed generality
   or higher. Its hypotheses are the printed setup or the conclusions of earlier sentences, and no
   binder stands for a cited result. The routes checked in detail:
   - `b7b49212cd37`:
     - "canonical trace is faithful, so stably finite" is
       `reducedGroupCStar_isStablyFiniteCStarAlgebra`, which rests on
       `ReducedGroupCStarTrace.canonicalFaithfulTracialState`.
     - "not MF by `prop:mf-residual-calculus`" goes `not_isMFAlgebra_reducedGroupCStar`, then
       `HasMFEmbedding.isCDEOperatorMF`, then `isCDEOperatorMF_of_faithful_corona_map`. The last is
       the `\leanverified` declaration of that lemma.
     - "since `Q` is not MF" is `manuscriptSentence_algebraNotCDEOperatorMF`, which uses the full
       residual and nontriviality.
   - `871771af6cba`: `manuscriptSentence_theoremHomsTrivial` uses the saturated clause of
     `manuscriptOneSidedCompressionCriterion`, which is the printed "last assertion".
     `manuscriptSentence_theoremQuotientTrivial` takes the previous sentence's conclusion as its
     hypothesis.
   - `92115dd7edef`: `exists_isNonDegenerate_isHypEmbedded` drops the countable and torsion-free
     hypotheses, so it is more general than the print. It rests on the closed
     `osinTheorem12Printed_unconditional`.

## Defects

1. **Fixed: `d29816e1de56`, L1705.** The printed clause is "the normal closure of `φ(S)` is
   `φ(N) = Q`".
   - `manuscriptSentence_theoremDefectEqTop` states neither this clause nor its route. It proves
     `𝔇_Q(φ(Γ)) = Q` by pulling back along `φ`.
   - The new carrier `TorsionFreeDefectNormalClosure.manuscriptSentence_theoremNormalClosureDefectEqTop`
     states all three clauses. Its closed form is
     `printedNormalClosureDefectEqTop : PrintedNormalClosureDefectEqTop`.
   - It follows the printed route: `Subgroup.map_normalClosure` for the surjection of
     `lem:saturation`, then normality plus `φ(S) ≤ 𝔇`.
   - The row correction is in `metadata/nm-census-rows/audit-sec5.tsv`, keyed `d29816e1de56`,
     because tex line 1705 holds two sentences and `LINE:1705` would be ambiguous.
2. **Doc only, forwarded to baseline-debt by the lead.** Some docstrings are stale, although the
   statements are correct.
   - The printed sentence now reads "not MF by Lemma `prop:mf-residual-calculus`", and the proof
     follows that route.
   - `manuscriptSentence_algebraNotMF` quotes a superseded sentence ("an embedding into a norm
     matrix corona would embed `Q` into the corona's unitary group").
   - `manuscriptSentence_algebraTrivialFiniteRadical` says "Only the last clause is carried … no
     vocabulary for hyperbolically embedded". The first clause is now carried by
     `exists_isNonDegenerate_isHypEmbedded`.
   - The docstring of `RegularNonMFAlgebra.DGOTheorem235Printed` carries the same stale paragraph.

## Rows owned by other lanes

- **`f2bf6328169e`, L1725.** `dgoTheorem235Printed` and `gerasimovaOsinTheorem11Printed` are
  closed and gated in `Audit/Sec5.lean`. The closed sentence
  `manuscriptSentence_algebraSimpleUniqueTraceStableRank_closed` lives in
  `TorsionFreeAlgebraSentencesClosed`, which is now root-wired. The row is `formalized`
  (`b0a084d16`).
- **The Hull rows at L1629–L1659** wait for the wall lanes. The cite-hull module
  `HullCitationSentences` is root-wired.

## Provenance and attribution rows

Three provenance rows make mathematical claims:

- `3113d5d90053` ("every norm-matrix model … kills the Clifford sign") is carried by census rows
  `9930600167a4` and `7732f82e8623`:
  `CliffordWitnessDirectDefect.manuscriptMapSignEqOneOfIsOperatorMFTarget` and
  `manuscriptCliffordWitnessNotIsOperatorMF`.
- `2b5a42f87cb2` ("the maximal group C*-algebra of a strictly compressed Kazhdan group is infinite")
  is carried by the `prop:max-infinite` rows `e681972f7114` and `a45c53bf93dd`.
- `1778c11e19e3` reports earlier Lean work, a historical claim, so it stays provenance.

The other provenance rows and both attribution rows make no mathematical claim.

# Part 2: the open W1 and W2 leaf Props

The audit ran at e374d0235 and was rechecked against aea484f30. Each Prop was checked at its stated
universes and generality against three questions:

- **Truth.** It was tested on degenerate diagrams: empty, one face, spurs, a boundary that is not a
  simple cycle, and multiply connected regions.
- **Reduction.** Is the reduction to the wall proved?
- **Route.** Does it follow the printed Hull/Osin route?

Each owner has the finding, and the lead has a summary.

## Refuted

- **`RegionShellingStatement`** (`VanKampen/FaceShelling.lean:194`) is refuted at `3f6eaff76`:
  `not_regionShellingStatement : ¬ RegionShellingStatement.{0, 0, 0}`, with
  `#audit_closed_axioms`.
  - **The map** is hull-respell's spur map: four darts, face cycles `[0,1,2]` and `[3]`, and the
    face set `{face 0}` with boundary cycle `[2]`.
  - **The proof.** By `shelling_invariant`, along a shelling every walk avoids dart 3 and holds one
    copy of dart 2 for each attached face, and after one face it holds dart 0. So no shelling
    ends at `[2]`.
  - **Consumers.** The binder at `Estimating/PieceConstruction.lean:83` is vacuous, and the
    `pasting` field of `ContiguityGeometry` supersedes it.
  - **Consequence for producers.**
    - `pasting` is a `FaceShelling`, which a singleton merged face has (`shelling_oneFace`).
    - A multi-face region whose G-faces carry spurs has none. For such a region, the `InnerGRegion`
      value must come from `FaceSetBoundary.cycle_value_eq_one_of_pasting` with a
      `FaceSetWordHomotopy`, not from `InnerGRegion.ofShelling`.
  - **Wiring.** Both spur modules are in the wire queue, the dependency first.
- **`FaceSetEarStatement` and `FaceSetEarDataStatement`** (`VanKampen/FaceSetPeelProducer.lean:171`)
  were refuted by hull-respell at `9dda53a05`, on the same map. They are off route.

## W1

The route is `OsinSection97PocketInputsStatement` (`Estimating/OsinAppendixLemma97Pocket.lean:42`).

- **Reduction.** The reduction to Lemma 9.7 and to the waist of Lemma 4.4 is proved:
  `osinSection97Inputs_of_pocketInputs`, `osinLemma97Section_of_pocketInputs` and
  `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputs`.
- **What the cut Props amount to.** At C-parameters the consumers use each cut only to reach
  `False`, so the cut Props say that a globally distinguished family has no multiple edges or no
  loops.

| Prop | Owner | Verdict |
|---|---|---|
| `MultipleEdgeCutInput` (`OsinAppendixSectionInduction.lean:76`) | hull-select | true modulo proof |
| `LoopCutInput` (`OsinAppendixSectionInduction.lean:86`) | hull-select, go-lemma42 | truth risk |
| `SectionPocketCutInput` (`OsinAppendixDescentCut.lean:71`) | unsettled (see 3) | plausible |
| `PhiPrimeCountInput` (`OsinAppendixEulerCount.lean:52`) | hull-euler | true modulo C6 |
| `OsinDescentStepInput` (`OsinAppendixAssemblyDescent.lean:94`) | nm-endpoints | off route; retire |

1. **`MultipleEdgeCutInput`** follows Osin 9.7 G2, and `ofRegionCut` matches it.
   - The `i ≠ j` binder landed at b45e7ef30. Both consumers now send the case `i = j` to
     `LoopCutInput`, so the truth risk of item 2 also covers that case.
   - The R-cell-free pocket goes to `false_of_collapse_singleton` (`OsinAppendixCutMerge.lean:120`).
     None of its inputs has a producer on main: an `InnerGRegion`, the merged
     `ContiguityGeometry` at `{R.merged}`, and `hweight`.
2. **`LoopCutInput` carries a truth risk.**
   - `OsinLoopCut` needs `0 < enclosed.rCellCount < Delta.rCellCount`. At a least-area diagram
     with one R-cell this cannot hold, so there the Prop says that no globally distinguished family
     has a loop.
   - **The risky configuration, a cap.** One G-region touches Π along two arcs separated by a short
     relator subword `t`, with a closing side `s` of length at most ε, and the pocket holds no
     R-cell.
   - Osin's printed loop case ("Ξ bounded by st") does not treat this configuration.
   - Merging gives no contradiction: there is one region, and weight and card are unchanged.
   - There is no formal counterexample, because the optimality of the family is global.
   - **Options sent to the lead:** exclude loops at the candidate level, weaken the conclusion, or
     prove an absorption lemma.
3. **`SectionPocketCutInput`** follows Osin 9.7(b), and `descentInput_of_sectionPocketCut` is
   proved.
   - The pocket with an R-cell goes through `fourSectionCuts_leastAreaCut` and the section
     transport. The carrier `OsinMultipleEdgeCut.ofPocketRegion` (45e7201da) needs one relator
     cell inside the pocket and one outside.
   - The R-cell-free or adjacent pocket needs the same merge producer as item 1.
   - **Ownership conflict.** dgo-analytic's report names hull-respell as the producer, while
     hull-respell's report says the lead's ~03:35 ruling superseded that.
4. **`PhiPrimeCountInput`.** `NoLoops` and `NoMultipleEdges` are binders, and the planar edge bound
   is proved. Step C1, `Φ'_M` with one outer vertex, landed unverified at 4e27d4965. C6, the empty
   two-gon, needs the same merge producer.
5. **`OsinDescentStepInput`.** Nothing on the live route consumes it.
   - Its binders include no `OsinCCondition` and no induction hypothesis, yet it must deliver a
     pocket cell above `1 − 11μ`.
   - dgo-analytic's Finding 3 reaches the same verdict.

**Proposal to the lead:** one shared piece Prop for the inputs of `false_of_collapse_singleton`,
serving items 1, 3 and 4.

## h94

- **The statement.** `no_connector` is retired (b8441172e), and `osinLemma94Section_of_pieces` takes
  the metric half and the planar half.
- **The metric half is closed:** `osinLemma94AntiparallelMetric` (sec5-sentences, e3da1ba60).
- **The planar half, `OsinLemma94PlanarRunInput`** (hull-unbound), has no refutation, and the
  degenerate cases pass (`ofNoUnbound`). Three obligations went to the owner:
  - backwards pairs on two sides that meet at a corner, with an end connector of length 0;
  - O-equivalent surgery to realize the geodesic connectors;
  - cutting paths `t_j` of minimal length, for the `quasiGeodesic` field.

## W2

The owners are hull-bridge and hull-component.

- **`QuotientPeripheralLetterPullbackStatement`** (`HullSCLemma51EmbeddedProducer.lean:122`) has no
  refutation.
  - p = [], W = ∅, empty `Lambda` and |p| = 1 all pass.
  - `IsBoundedLemma44Input.lengthBounded` gives uniformity in W.
- **Reduction.** M1, `.or`, the induction and `quotientPeripheralLetterPullbackAt_of_letterStepBound`
  are proved. The leaf M2 (CutOutcome, Cut, Holds) is not on main.
- **Gap.** `CutFace` (`HullSCLemma51LetterPullbackCutFaces.lean:207`) does not carry what M2 needs:
  - it has no `rem`;
  - `ext_sub` only puts the letters of `ext` in some relator;
  - `short` is only `|L| + |R| < |arc|`;
  - the module docstring claims `ext ++ rem ∈ W`, which the fields don't state.

  M2 needs the decomposition and `|L| + |rem| + |R| < |arc|`. The inequality is already proved by
  `exists_long_cut_of_certificate` (`HullSCLemma51LetterFacts.lean:90`).
- **Route.** The letter moves are designed in the repo rather than taken from the printed proof of
  DGO 4.24, so fidelity rests on the endpoint statement.

# Open

- **The lead:**
  - rule on `LoopCutInput`;
  - retire `OsinDescentStepInput`;
  - assign the shared merge producer;
  - settle who owns `SectionPocketCutInput`;
  - wire the two spur modules.
- **baseline-debt:** the stale docstrings of defect 2, and `FaceShelling.lean:190` ("The one planar
  fact still missing").
- **hull-unbound:** the stale docstring at `SurgeryInnerCollapse.lean:17-21`.
- **Wall lanes:** the Hull partial rows.
