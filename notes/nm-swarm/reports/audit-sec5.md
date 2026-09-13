# audit-sec5 lane report

Lane `audit-sec5` audits tex 1621–2022 of `non_mf_groups_exist.tex`: `sec:torsion-free`,
Origin and authorship, and Acknowledgments.

## Landed

- `8a7de88a6`: probe GREEN (tag `0913-015553-23837`, BUILT both modules). The green bytes are
  identical to main, and both modules are on the wire queue (carrier first):
  - `GroupApproximation/Manuscript/NonMF/Audit/Sec5.lean`, the permanent gate. It runs
    `#audit_closed_axioms` on the named-Prop endpoints and `#audit_axioms` on every other
    carrier the census names for this range, together with the route theorems they rest on.
  - `GroupApproximation/Manuscript/NonMF/TorsionFreeDefectNormalClosure.lean`, the carrier for
    the clause that row `d29816e1de56` was missing (defect 1 below).

## The rows in range

There are 53 census rows: 3 structural, 1 definition, 15 formalized, 13 partial, 19 provenance and
2 attribution.

1. **Reachability.** Every declaration named by the 16 formalized and definition rows exists on
   origin/main (9f819ad8c) in a module the root reaches. The modules are
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

1. **Fixed: `d29816e1de56`, L1705.** The printed clause is "the normal closure of `φ(S)` is `φ(N) = Q`".
   `manuscriptSentence_theoremDefectEqTop` states neither this clause nor its route. It proves
   `𝔇_Q(φ(Γ)) = Q` by pulling back along `φ`.
   - The new carrier `TorsionFreeDefectNormalClosure.manuscriptSentence_theoremNormalClosureDefectEqTop`
     states all three clauses.
   - Its closed form is `printedNormalClosureDefectEqTop : PrintedNormalClosureDefectEqTop`.
   - It proves the conclusion by the printed route: `Subgroup.map_normalClosure` for the surjection
     of `lem:saturation`, then normality plus `φ(S) ≤ 𝔇`.
   - Row correction: `metadata/nm-census-rows/audit-sec5.tsv`, keyed `d29816e1de56`. Tex line 1705
     holds two sentences, so `LINE:1705` would be ambiguous. The merge grades the row `partial` until
     the carrier module is wired, then restores `formalized`.
2. **Doc only, reported to the lead:** some docstrings are stale, although the statements are
   correct. Both files are in `baseline-debt.files`, so this lane does not edit them. The printed
   sentence now reads "not MF by Lemma `prop:mf-residual-calculus`", and the proof follows that
   route.
   - `manuscriptSentence_algebraNotMF` quotes a superseded sentence ("an embedding into a norm
     matrix corona would embed `Q` into the corona's unitary group").
   - `manuscriptSentence_algebraTrivialFiniteRadical` says "Only the last clause is carried … no
     vocabulary for hyperbolically embedded". The first clause is now carried by
     `exists_isNonDegenerate_isHypEmbedded`.
   - The docstring of `RegularNonMFAlgebra.DGOTheorem235Printed` carries the same stale paragraph.

## Partial rows (owned by other lanes): pending upgrades

- `f2bf6328169e`, L1725: `dgoTheorem235Printed` and `gerasimovaOsinTheorem11Printed` are closed and
  reachable from the root, and both are gated in `Audit/Sec5.lean`. The closed sentence
  `manuscriptSentence_algebraSimpleUniqueTraceStableRank_closed` lives in
  `TorsionFreeAlgebraSentencesClosed`. That module is on main but not reachable from the root and
  not in the wire queue.
- The Hull rows at L1629–L1659 wait for the wall lanes. The cite-hull module
  `HullCitationSentences` is queued (18de0ce6a).

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

## Open

- Wiring, by the lead: `TorsionFreeDefectNormalClosure`, then `Audit.Sec5`, both queued at `8a7de88a6`.
- `baseline-debt`: the stale docstrings in defect 2.
- `nm-endpoints`: `TorsionFreeAlgebraSentencesClosed` is on main, but no compiled-evidence record
  from that lane names it and it is not queued. Wiring it would let `f2bf6328169e` be upgraded.
- Wall lanes: the Hull partial rows.

Apart from these, this lane's scope is finished.
