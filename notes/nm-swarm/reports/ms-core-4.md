# Lane ms-core-4: sentence ledger for thm:core-ring-reflection (tex 1516–1540)

Range: `non_mf_groups_exist.tex` at origin/main 68481e4d7, lines 1516–1540, `\label{thm:core-ring-reflection}` and its proof.
This lane audits and fills unowned leaves only. The owner of the theorem is chain-reflection
(`notes/nm-swarm/reports/chain-reflection.md`, rows `metadata/nm-census-rows/chain-reflection.tsv`).
The theorem text did not change in 73a84cd9c; its lines only moved down by 2. So chain-reflection's 12 keys are current.

## Ledger (checked at origin 19d96c2c5)

| # | tex | sentence (abridged) | key | owner | carriers on main | row status |
|---|---|---|---|---|---|---|
| 1 | 1518–1519 | every unital hom `R_X → A`, `A` directly finite, factors uniquely through `R_X → R_Y` | `42c043ef7ab5` | chain-reflection | `IsUniversalDirectlyFiniteQuotient`, `isUniversalQuotients_of_surjective` | partial |
| 2 | 1519–1520 | also the universal stably finite and LEF ring quotient | `8981cd70915a` | chain-reflection | `IsUniversalStablyFiniteQuotient`, `IsUniversalLEFQuotient`, `isUniversalQuotients_of_surjective` | partial |
| 3 | 1520–1521 | the same for `M_m(R_X) → M_m(R_Y)`, every `m ≥ 1` | `43afa4ee3f10` | chain-reflection | `isUniversalQuotients_mapMatrix`, `mapMatrix_surjective_of_surjective` | partial |
| 4 | 1521–1523 | `R_X` DF ⇔ SF ⇔ LEF ⇔ every point chain recurrent | `cfbacaa0fffa` | chain-reflection | `directlyFinite_iff_stablyFinite_iff_lef_iff_injective` | partial |
| 5 | 1527–1529 | a unital hom to a DF ring kills every `d`, hence all of `I` | `9dae685e37b9` | chain-reflection | `KillsKernelOfDirectlyFinite` | partial |
| 6 | 1529–1530 | `R_Y` LEF, hence SF; all three universal properties follow | `400dde0dbd9d` | chain-reflection | `isUniversalQuotients_of_surjective`, `existsUnique_comp_eq_of_surjective` | partial |
| 7 | 1531–1532 | amplification: `φ : M_m(R_X) → A` unital, `e = φ(E_11)` | `5a62e295ac1a` | chain-reflection | `matrixUnitCornerHom`, `isIdempotentElem_map_single_one` | definition |
| 8 | 1532–1533 | `eAe` is DF: extend a one-sided inverse pair by `1 − e` | `d74779471003` | chain-reflection | `isDedekindFiniteMonoid_corner`, `oneSubAddCornerHom_injective` | formalized |
| 9 | 1534–1535 | apply the argument to `r ↦ φ(rE_11)` into the corner | `715cbd0f3410` | chain-reflection | `matrixUnitCornerHom`, `map_eq_zero_of_forall_entry_mem` | partial |
| 10 | 1535–1536 | the other matrix units show `φ` kills `M_m(I)` | `30a44485e5e8` | chain-reflection | `map_eq_zero_of_forall_entry_mem`, `killsKernelOfDirectlyFinite_mapMatrix` | partial |
| 11 | 1536–1537 | `M_m(R_Y)` is LEF, entrywise from finite ring tables | `f2baa4a46f78` | chain-reflection | `Pestov91.IsLEFRing.matrix`, `isUniversalQuotients_mapMatrix` | partial |
| 12 | 1538 | `I = 0` exactly when `X = Y`, giving the equivalences | `b23e0f5197b5` | chain-reflection | `directlyFinite_iff_stablyFinite_iff_lef_iff_injective` | partial |

Twelve sentences, twelve keys, every one owned. No sentence of the range is missing from a key map.

## Verification

- `Algebra/DirectlyFiniteCorner` and `Algebra/DirectlyFiniteReflection` are root-imported (`GroupApproximation.lean`
  l.5151, l.5161). They carry 3 and 7 audit lines respectively.
- `Pestov91.IsLEFRing.matrix` (`Pestov91/LEF.lean:207`, root-imported) follows the printed route: it takes the finite
  set of entries and partial row-column sums, the LEF model of the coefficient ring, and `M ↦ M.map φ`. That is
  "entrywise from finite ring tables". The module has no audit line, but it is an intermediate lemma, not an endpoint.
- Printed claims checked by hand; nothing is false as stated:
  - uniqueness of the factorization needs `R_X → R_Y` surjective (lem:transient-matrices proof, tex 1482);
  - the stably finite and LEF universal properties reduce to the directly finite one, because stably finite ⇒ DF and
    LEF ⇒ DF, together with `R_Y` LEF ⇒ SF;
  - `M_m(R_Y)` is SF because `M_n(M_m(R_Y)) ≅ M_{nm}(R_Y)`;
  - in `r ↦ φ(rE_11)` the identity of the corner is `e = φ(E_11)`, so the map is unital into `eAe`;
  - `I = 0 ⇒ X = Y`: if `X ≠ Y`, the open set `X∖Y` contains a nonempty clopen `C`, and `1_C` is a nonzero element of `I`.
- The rows cannot flip until the residuals below close. Infinite `X` blocks `decide`-style model tests, and
  chain-reflection's module 2 already carries finite-model tests (`lefInterfaces_finite_model`,
  `reflection_hypotheses_finite_model`, `not_killsKernelOfDirectlyFinite_toZero`).

## Residuals of the range (all owned; none built here)

| residual | discharged by | owner | state at 19d96c2c5 |
|---|---|---|---|
| `LEFStablyFiniteInterface` (LEF ⇒ SF) | chain-core S1 item 3 | hull-bridge (ruling 16:00–16:17) | not on main; no mention in hull-bridge.md |
| restriction `R_X → R_Y` | `ClopenCrossedProduct.restrict` | chain-core | LANDED 067b40a5e (ClopenCrossedProductComap) |
| `d` killed by DF targets | `map_defectD_eq_zero`, `restrict_defectD_eq_zero` | chain-core | LANDED 32275d037, a55be3025 |
| surjectivity of restriction | `restrict_surjective` | chain-matricial (ruling 16:25) | planned |
| `ker = I`, `I` generated by defects | `ker_restrict_le_of_forall_defectD`, `transientIdeal_eq_span_defects` | chain-matricial | planned |
| `I = 0 ⇔ X = Y` | `transientIdeal_eq_bot_iff`, `restrict_injective_iff` | chain-matricial | planned |
| `R_Y` LEF | `isLEFRing_crossedProduct_chainRecurrentSet` | chain-itinerary | planned (module 6, ChainCoreGeneral) |
| printed assembly `PrintedCoreRingReflection` | module 3 of chain-reflection | chain-reflection | later |

## Claims

No piece of tex 1516–1540 is unowned, so this lane builds nothing there and appends no census rows for that range,
which would duplicate chain-reflection's keys.

Next item (lead ruling 09-13 ~17:00): chain-core S1 items 3, 4 and 7, which the 16:00–16:17 ruling gave to
hull-bridge. The ownership check at origin a2cb17f58 found no hull-bridge in-flight file, no shared-tree draft, no
landing on them since the ruling, and no mention in hull-bridge.md.

CLAIM item-3 GroupApproximation/Algebra/LEFRingStablyFinite.lean
- tex 1358–1359: "Finite inverse-pair tables show that LEF rings are stably finite."
- LEF ⇒ directly finite ⇒ stably finite, by way of `Pestov91.IsLEFRing.matrix`.
- Also discharges chain-reflection's `LEFStablyFiniteInterface`.

CLAIM item-4 GroupApproximation/Algebra/LEFRingStablyFinite.lean
- tex 1359–1362: "Entrywise finite ring models, including the entries of inverse matrices, show that their general
  linear groups are LEF. Countable LEF groups are MF".
- GL_n of an LEF ring is LEF; countable GL_n is MF through `isOperatorMF_of_isLEF`.

CLAIM item-7 GroupApproximation/Dynamics/ClopenCrossedProductCountable.lean
- tex 1647–1649: "Its countability hypothesis holds because X has a countable clopen basis and each clopen subset is a
  finite union of basis sets."
- Producer of ct-bilateral-mf's `ClopenCrossedProductCountableStatement` (BilateralThreeStatement, 816a6b699) and of
  ct-rank-budget's `CountableCrossedProductStatement`.

## Landed (items 3, 4, 7 closed)

Module `GroupApproximation.Algebra.LEFRingStablyFinite`, LANDED 5932d213f (probe GREEN 0913-172320-48885), queued for wiring:
- `Pestov91.IsLEFRing.isDedekindFiniteMonoid`, `Pestov91.IsLEFRing.isStablyFiniteRing`;
- `lefStablyFiniteInterface : LEFStablyFiniteInterface` (chain-reflection's residual);
- `Pestov91.IsLEFRing.isLEF_generalLinear n : IsLEF (Matrix n n A)ˣ`;
- `Pestov91.IsLEFRing.isOperatorMF_generalLinear [Countable A] n : IsOperatorMF (Matrix n n A)ˣ`;
- closed endpoints `printedLEFRingsStablyFinite`, `printedGeneralLinearGroupsOfLEFRingsLEF`, `printedCountableLEFGroupsMF`.

Module `GroupApproximation.Dynamics.ClopenCrossedProductCountable`, LANDED 7dceca26d (probe GREEN 0913-173055-72684), queued:
- `exists_finite_subset_sUnion_eq_of_isClopen` (any basis of a compact space), `exists_countable_clopen_basis`,
  `countable_setOf_isClopen`, `countable_locallyConstant [Countable k]`;
- `ClopenCrossedProduct.countable T k` for compact second countable `X` and countable ring `k`;
- closed endpoints `printedCountableClopenBasis`, `printedClopenCrossedProductCountable`.

Module `GroupApproximation.Manuscript.ChainCore.ClopenCrossedProductCountableConsumers`, LANDED 7dceca26d, queued:
- `clopenCrossedProductCountableStatement : BilateralThree.ClopenCrossedProductCountableStatement`;
- `countableCrossedProductStatement : DynamicRankBudget.CountableCrossedProductStatement`.
- The wrappers sit in their own module because it imports both consumer modules. Consumers import the light producer
  module directly, so no import cycle arises.

Census rows `metadata/nm-census-rows/ms-core-4.tsv`: `b1a4887c5412`, `1d0bcc92a75f`, `1a88ddc187c0`, `7e27335fac44`
(the countability sentence's current key; `6e533530564d` hashed the wording before 73a84cd9c).

## Next item (lead ruling 09-13 ~17:50): second start on chain-matricial module 5

Ownership check at origin 654a053ae:
- chain-matricial's TransientIdealExact.lean is identical on disk and origin: no in-flight second half, and no
  TransientIdealMatricial.lean anywhere.
- theoremc-retire holds only the inputs (LocallyConstantClosedExtension and PartialShiftClasses; GREEN 0913-173317-80780,
  not landed).
- The other recent `transientIdeal` files (ms-compress-3 ClopenCrossedProductAlgebra, ms-units CoreKernelFTwo) state
  consumer Props only.

CLAIM transient-ideal-generation GroupApproximation/Dynamics/TransientIdealDefectSpan.lean
- tex 1476–1487: "is generated by the indicators $1_{P\setminus T(P)}$ of the defects" and "The translates of the defects
  cover that complement; a finite clopen subdivision subordinate to this cover on each compact coefficient support proves
  the ideal-generation claim".
- An additive producer under names different from chain-matricial's planned `transientIdeal_eq_span_defects`.

CLAIM transient-ideal-locally-matricial (second start)
- Waits until theoremc-retire lands modules 2 and 4, which it consumes.
