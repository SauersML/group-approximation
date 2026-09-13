# baseline-debt lane report

Lane `baseline-debt`, roster section `## baseline-debt`. The census findings are in
`metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt`, and line numbers below point into that
file at origin/main 0af6e2373. Census rows: `metadata/nm-census-rows/baseline-debt.tsv`.

## Landed

- `95e6d09ca`: three new modules, landed unverified. They are unchanged since then except
  for a one-name fix in `StrongConvergenceMFSubsingleton`.
- `296386753`: the four modules below, from probe 0913-021321-7359. The probe reported
  `PROBE GREEN` and COMPILED all four overlay files:
  - `StrongConvergenceMFSubsingleton` was rebuilt;
  - the other three were replayed with the same input hash, after they were BUILT in probe
    0913-020324-57087.
  - The `#audit_axioms` and `#audit_closed_axioms` lines show only `propext`,
    `Classical.choice` and `Quot.sound`.
  - The three new modules are queued for wiring.

| module | declarations |
|---|---|
| `Manuscript/NonMFSentences/FullDefectPairLeavitt.lean` (new) | `fullDefectPair_aryLeavittAlgebra`, `fullDefectPair_aryLeavittAlgebra_zmodTwo` |
| `Sofic/StrongConvergenceMFSubsingleton.lean` (new) | `isStronglyOperatorMF_of_subsingleton`, `isStronglyOperatorMF_unit` |
| `Manuscript/NonMF/NaiveFreeProductPropertyOfAcylindricallyHyperbolic.lean` (new) | `naiveFreeProductProperty_of_isAcylindricallyHyperbolic`, `powersAveragingEstimate_of_isAcylindricallyHyperbolic` |
| `Manuscript/NonMF/TorsionFreePrintedSentences.lean` (edited) | `PrintedTheoremQuotientTrivial`, `manuscriptSentence_theoremQuotientTrivial : PrintedTheoremQuotientTrivial` |

## Findings closed

- **(a) open-predicate `FullDefectCornerRemark.manuscriptSentence_cornerPassesUp`**
  (baseline 238, tex 1008).
  - The premise `FullDefectPair (Corner R p hp)` is the printed hypothesis of the sentence:
    "the ring pRp, with unit p, satisfies the hypothesis".
  - `FullDefectPair` now has an honest producer. At `L_k(1,d)` with `d ≥ 2`, take
    `s = s₀`, `t = t₀`; then `t₁(1 - s₀t₀)s₁ = 1`. It is closed at `L_{𝔽₂}(1,2)`.
  - So the finding retires as an honest discharge, and no reclassification is needed.
- **(b) inlined-statement `TorsionFreePrintedSentences.manuscriptSentence_theoremQuotientTrivial`**
  (baseline 171, tex 1711-1716).
  - The theorem is now the closed endpoint `PrintedTheoremQuotientTrivial`, with no
    binders.
  - The endpoint quantifies over `Q` and `L` with property (T) and full defect, and over
    a surjection `r` onto an MF group `Q̄`. It concludes `r` is trivial and `Q̄ = 1`.
  - It is proved from `manuscriptSentence_theoremHomsTrivial`.
  - On main, no proof uses the old statement. The only Lean reference is
    `#audit_axioms` in `Manuscript/NonMF/Audit/Sec5.lean`, and the new name
    `PrintedTheoremQuotientTrivial` has no duplicate.
- **(c) open-predicate `ReducedGroupCStarTrace.powersAveragingEstimate_of_naiveFreeProductProperty`**
  (baseline 298, tex 1725).
  - `NaiveFreeProductProperty G` is now produced at countable acylindrically hyperbolic `G`
    with `HasTrivialFiniteRadical G`, from the closed `naiveFreeProductAtAcylindricallyHyperbolic`.
  - The premises of that producer have closed producers:
    - `instIsAcylindricallyHyperbolicFreeGroupFinTwo`;
    - `hasTrivialFiniteRadical_of_torsionFree` together with `isPowerTorsionFree_multiplicative_int`.
- **(d) carrier-data `IsStronglyOperatorMF` (baseline 78) and open-predicate
  `IsStronglyOperatorMF.isOperatorMF` (baseline 97)**, tex 99 (printed 102-105).
  - Verified: `not_isStronglyOperatorMF_of_not_isOperatorMF` is the printed contrapositive
    ("a group that is not MF as defined here is not MF in that convention either").
  - The carrier now has an honest producer: a trivial group is strongly MF.
    - The models are one-point, and every element maps to `1`.
    - Both norms equal `|∑ c_g|`.
  - It is closed at `Unit`.

## (e) carrier lines and (f) remaining open-predicate findings: classification

Only the four walls below produce each carrier. The residue is exact; nothing else in
these findings is a citation.

- Owned by `hs-vanishes`: 66 `manuscriptPrintedNormalKazhdan` and 79 `HSVanishes`.
- Owned by `nm-endpoints`: 203 `TheoremC.Configuration`, and every `_of_leastAreaLeaves`
  finding (214, 218, 227, 230, 247, 250, 253, 257, 259, 263, 265, 268, 272, 276, 278, 286,
  289, 294).
- Four walls exactly:
  - carrier lines:
    - 212 `PrintedTorsionFreeTheorem`, 216 `PrintedTorsionFreeTheoremOsin`;
    - 283 `FournierFacioParagraph`;
    - 296 `PrintedRegularNonMFAlgebra`, 297 `PrintedRegularNonMFAlgebraOsin`;
  - 220/223 `manuscriptTorsionFreeTheorem(Osin)_of_hullLeaves`;
  - 232/235 `manuscriptRegularNonMFAlgebra(Osin)_of_hullLeaves`. Their extra premises `hDGO`
    and `hGO` have closed producers, `simpleUniqueTraceAtHypEmbedded_closed` and
    `gerasimovaOsinTheorem11Printed`;
  - 301/304/307 `manuscriptRegularNonMFAlgebra{,Osin,LimitSet}_of_hullLeaves_closedGO`.
- Greendlinger and bridge walls only:
  - 245, 249, 252 `PrintedHullSmallCancellation{Current,Osin,LimitSet}`;
  - 267 `PrintedSaturationLimitSet`;
  - 281 `GGT.RelHyp.osin24HullStep_of_boundedLeaves`. Its three premises
    `HullSC.BoundedHullLemma44CanonicalQuotientStatement.{0}`,
    `HullSC.BoundedImageEmbeddingStatement.{0,0}` and `HullSC.HullLemma49KernelPowerStatement.{0,0}`
    are produced over the least-area spelling. That spelling needs the Greendlinger wall
    plus the closed `relativeDiscRealizationSpellingStatement` and
    `relativeExteriorArcConversionAtWordRotatedStatement`, and the bridge wall.

## Residual statements (exact)

1. `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`
2. `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}`
3. `TheoremC.KotowskiOllivierStatement`
4. `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`

These are walls owned by other lanes: hull-*, kh-* / ko-closed, and simple-group.

## Next

- Census: the retirements need a census merge.
  - Five findings are retired by honest producers: baseline 78, 97, 238, 298, and the
    signature change at 171.
  - The merge must see the landed producers; the gate reads all of `GroupApproximation/**`,
    so wiring is not needed for it.
- Wiring: three modules are queued.
