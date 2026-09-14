# Lane ms-core-1: the sec:chain-core opening (tex 1338–1370 at origin/main 68481e4d7)

Scope: a sentence ledger, model tests, and unowned leaves only (Brief C of the wave-2 roster).
- Keys come from the census worklist, merge 0913-160921. Its line numbers are 2 lower than at 68481e4d7.

## Ledger

| key | tex | sentence (abridged) | owner | carriers on origin/main | status | note |
|---|---|---|---|---|---|---|
| `d59fc0887768` | 1341 | the torsion-defect argument can identify the whole MF radical even when the defect ideal is proper | chain-core | none | unassigned | waits for chain-radical's thm:core-mf-radical endpoint (chain-core.md) |
| `753b90beed12` | 1342 | such a computation for algebraic crossed products from zero-dimensional dynamics | chain-core | `ClopenCrossedProduct` | structural (row landed) | |
| `275bedb28f9f` | 1345 | X nonempty compact metrizable zero-dimensional, T a homeomorphism | chain-core | `ClopenCrossedProduct T k` over `T : X ≃ₜ X` | unassigned | the module states that the printed hypotheses belong to the theorems that use them |
| `752564275a33` | 1346–1349 | for a finite field k, R_X = LC(X,k) ⋊_T ℤ with u f u⁻¹ = f ∘ T⁻¹ | chain-core | `ClopenCrossedProduct`, `coeff`, `unit`, `unit_mul_coeff_mul_inv` | unassigned | definition, stated for every ring k |
| `a1bda19b475a` | 1351–1353 | LC means locally constant; the crossed product is algebraic, with unique finite Laurent expansions | chain-core | existence: `exists_sum_coeff_mul_unit_zpow` | unassigned | no uniqueness lemma on origin; the docstring asserts uniqueness by construction (finitely supported ℤ → LC(X,k)) |
| `8a557cb954fb` | 1353–1354 | the powers of u remain formal even if T has finite order | chain-core | by construction (`SkewMonoidAlgebra`) | unassigned | no lemma `unit ^ i = unit ^ j → i = j` on origin |
| `6011dc411b20` | 1354–1357 | the printed LEF ring definition | chain-core (S1 leaf 2, next) | `Pestov91.IsLEFRing` | unassigned | model test 1 |
| `2d1ca8689ac6` | 1357–1358 | a group is LEF with the analogous multiplicative definition | chain-core | `Sofic.IsLEF` (targets `Equiv.Perm (Fin n)`) | unassigned | finite-group and permutation targets agree (Cayley) |
| `b1a4887c5412` | 1358–1359 | finite inverse-pair tables show LEF rings are stably finite | hull-bridge (ruling 16:17, S1 item 3) | none: `LEFStablyFiniteInterface` (Algebra/DirectlyFiniteReflection) has no producer | unassigned | model test 2 |
| `1d0bcc92a75f` | 1359–1360 | entrywise finite ring models show GL_n of an LEF ring is LEF | hull-bridge (S1 item 4) | `IsLEFRing.matrix`, `IsLEFRing.isLEF_units` | unassigned | `(hA.matrix (Fin n)).isLEF_units` gives LEF of `(Matrix (Fin n) (Fin n) A)ˣ` |
| `1a88ddc187c0` | 1361–1362 | countable LEF groups are MF, by the regular representations of the local models | hull-bridge (S1 item 4) | `isOperatorMF_of_isLEF [Countable G]` (Sofic/LocallyFiniteMF) | unassigned | `IsOperatorMF` is the corona form. The printed MF definition (tex 87–98, CDE) is the asymptotic-unitary form, and the bridge lies in ms-intro-1's range |
| `49f76a64907a` | 1364–1367 | chain recurrent, for a compatible metric | hull-euler (S2) | `IsMetricChainRecurrent`, `isChainRecurrent_iff_metric`, `isMetricChainRecurrent_iff_of_compact` (20911e5b2) | unassigned | the printed chain x_0, …, x_r with r ≥ 1 matches `TransGen (ChainStep T V)` |
| `d5af28721656` | 1367–1368 | Y = CR(T) | hull-euler (S2) | `chainRecurrentSet`, `chainRecurrentSet_eq_of_compact` | unassigned | definition; independence of the metric on compact X is landed |
| `3ebdab1c418b` | 1368–1369 | we first construct this set in a form that also supplies finite ring models | hull-euler (S2) | none | unassigned | structural |

## Model tests (by argument; no printed claim in this range is false)

1. **The printed LEF definition is equivalent to `IsLEFRing`.** The printed definition preserves the sums and products that stay in the subset, and preserves 0 and 1 when present. `IsLEFRing` preserves 0, 1 and every pairwise sum and product of the subset.
   - `IsLEFRing` ⇒ printed is immediate.
   - Printed ⇒ `IsLEFRing`: apply the printed definition to t′ = t ∪ (t + t) ∪ (t · t) ∪ {0, 1}. Every pairwise sum and product of t stays in t′.
2. **LEF rings are stably finite.**
   - Take a, b ∈ M_n(A) with ab = 1.
   - `IsLEFRing.matrix` gives a finite model φ of M_n(A) that is injective on {a, b, ab, ba, 1}.
   - Finite rings are directly finite, so φ(b)φ(a) = 1 = φ(1). Injectivity then gives ba = 1.
3. **The powers of u are formal.** For T = id on a point and k = F_2, R_X = F_2[u, u⁻¹], and the u^j are pairwise distinct.

## Unowned leaves

None in this range.
- Every key has an owner. The S1 keys are listed in the census chain-owners table; the S2 keys and hull-bridge's items 3, 4 and 7 are set by the roster rulings of 16:00–16:17.
- Nothing was built, and no census rows were appended.

## Claims

- SKIPPED (never claimed on main): uniqueness of Laurent expansions and formal powers of u in `ClopenCrossedProduct T k`
  (keys `a1bda19b475a`, `8a557cb954fb`). Assigned by main 09-13 ~17:10.
  - The first ownership check (origin b39b4b5a1, ~17:09) found no draft.
  - The re-check at 17:21 (origin ebd2a858c) found chain-core's in-flight `GroupApproximation/Dynamics/ClopenLaurent.lean`
    (mtime 17:14, listed in `chain-core.files`, not yet probed or landed). It covers both keys: `laurentSum`,
    `coeff_mul_unit_zpow`, `laurentSum_coeff`, `laurentSum_injective`, `laurentCoeff`, `existsUnique_laurentSum`,
    `unit_zpow_injective`, and the closed endpoints `printedLaurentExpansionsUnique` and `printedPowersFormal`.
  - No module was written. The path `Dynamics/ClopenCrossedProductLaurentUnique.lean` is removed from `ms-core-1.files`.
  - Nearby, and a different statement: ct-rank-two-limit's `Dynamics/ClopenCrossedProductLaurentEval.lean` evaluates R_X at
    points of period at most two.

- CLAIM (09-13 ~17:40, assigned by main): help ct-return-tower close `ReturnRingCrossedProductStatement`
  (`Dynamics/ReturnTowerStatements`, 4d2084188; tex 1721–1726): `P_C = p_C R_X p_C ≃+* LC(C,k) ⋊_{S_C} ℤ`.
  - Split agreed with ct-return-tower (its reply ~17:45). ms-core-1 takes:
    1. the ℤ-crossed-product lift over `SkewMonoidAlgebra.liftNCRingHom` (`Algebra/ZCrossedProductLift`: `liftOfUnit`,
       `covariant_zpow`, `ringHom_ext`);
    3. injectivity and surjectivity (splitting partial shifts along returns);
    4. the closed `returnRingCrossedProductStatement_holds`, in `Dynamics/ReturnRingCrossedProduct.lean`.
  - ct-return-tower owns item 2, the return unitary and covariance (`Dynamics/ReturnRingUnit`: `returnP`, `ReturnCorner`,
    `returnV`, `returnW`, `returnUnit`, `returnV_mul_coeff_extend`). It also keeps `Dynamics/ReturnCells`. Items 3 and 4
    consume both once they are on origin.
  - 09-13 ~18:05: main moved SURJECTIVITY to ct-return-tower (`Dynamics/ReturnCornerGeneration`,
    `surjective_of_generators`). The ms-core-1 surjectivity draft was withdrawn unlanded, and a copy is kept in the lane
    backup.

- CLAIM (09-13 ~18:35, assigned by main): the induced-core remainder of cor:dynamic-rank-budget (tex 1743–1750), agreed with
  ct-rank-budget in one message. ct-rank-budget's landed `DynamicRankBudgetInducedCore` has `CR(S_C) ⊆ C ∩ Y` by a direct
  chain argument and marks the rest "remain to be formalized". ms-core-1 takes:
  1. `C ∩ CR(T) ⊆ CR(S_C)` along the printed route: the return ring of `C ∩ Y` is a corner of the LEF ring `R_Y`, hence LEF,
     then thm:core-ring-reflection. Stated over `CoreRingReflectionStatement` and `CoreModelsLEFStatement`.
  2. A direct unconditional proof of the same inclusion.
  3. The printed saturation route for `CR(S_C) ⊆ C ∩ Y`.
  4. The closed equality.
  - Modules: `Algebra/CornerLEF` (a corner of an LEF ring is LEF), plus new
    `Manuscript/NonMFSentences/DynamicRankBudgetInducedCore*` and `Dynamics/ReturnSection*` helpers.
  - ct-rank-budget keeps `ReturnTransientIdealStatement`, placement, ReturnKernel, the bridge and packaging.
  - LANDED `Algebra/CornerLEF` 4ce7498e3 (probe 0913-183811-89839 GREEN): `Pestov91.IsLEFRing.corner`.
  - LANDED `Manuscript/NonMFSentences/DynamicRankBudgetInducedCoreReverse` c56f96a99, verified by probe 0913-184151-5011 GREEN
    on the same bytes.
    - `isReturnSection_restrict`, `returnTime_restrict`, `firstReturnHomeomorph_restrict_coe`.
    - `mem_chainRecurrentSet_firstReturn_of_pieces`: `C ∩ CR(T) ⊆ CR(S_C)`, printed route.
    - `image_chainRecurrentSet_firstReturn_of_pieces`: `CR(S_C) = C ∩ CR(T)`.
    - Both take only `CoreRingReflectionStatement` and `CoreModelsLEFStatement` as premises.
    - Process slip: the first landing used `NM_UNVERIFIED` for a Lean file, and main was told.
  - LANDED `Dynamics/ReturnSaturation` and `Manuscript/NonMFSentences/DynamicRankBudgetInducedCoreSaturation` afa5cd02d
    (probe 0913-192008-75631 GREEN).
    - `mem_of_zpow_mem`: orbit visits to `C` are successive returns.
    - `returnSaturation`, `image_returnSaturation`, `mem_returnSaturation_iff`, `returnSaturation_eq_biUnion`,
      `isClosed_returnSaturation`.
    - `coe_mem_chainRecurrentSet_of_firstReturn_of_pieces`: `CR(S_C) ⊆ C ∩ CR(T)`, printed saturation route (tex 1745–1749).
    - `image_chainRecurrentSet_firstReturn_printed`: `CR(S_C) = C ∩ CR(T)`, both inclusions on the printed route.
    - Both take only `CoreRingReflectionStatement` and `CoreModelsLEFStatement` as premises.
  - Claim complete. The optional item (a direct unconditional proof of `C ∩ CR(T) ⊆ CR(S_C)`) is not started: it is off the
    printed route and changes no census grade.
  - Lean traps from this item:
    - a subtype term `⟨f x, h⟩` carries a proof whose type mentions `f x`. `rw` inside `Subtype.ext` fails with "motive is
      not type correct", so `show` the plain equation first.
    - `Dynamics.mapsTo_chainRecurrentSet` applied straight to a membership mis-infers the map. State the `MapsTo` with
      its type written out.

## ReturnRing modules (ms-core-1)

| module | contents | status |
|---|---|---|
| `Algebra/ZCrossedProductLift` | `unitPowHom`, `covariant_zpow`, `liftOfUnit` (`_single`, `_C`, `_unit_zpow`, `_unit`, `_sum_C_mul_unit_zpow`), `ringHom_ext` | LANDED 8c0e01a29 (probe 0913-174102-15223 GREEN) |
| `Algebra/ZCrossedProductDegree` | `DegreesGE`/`DegreesLE`, closure under sums, products and powers, monomials, degree-zero readout | LANDED 69cfc53ff (probe 0913-182552-29572 GREEN) |
| `Dynamics/ReturnRingLift` | `extendCorner`, `returnCoeffHom`, `returnUnit_mul_returnCoeffHom`, `returnRingHom` (θ), `coe_returnRingHom_coeff` / `_unit` / `_unit_inv` / `_unit_zpow` | LANDED 69cfc53ff |
| `Dynamics/ReturnRingInjective` | `cellCoeff_zero`, `degreesGE_one_returnV`, `degreesLE_neg_one_returnW`, `coeff_one_coe_returnRingHom`, `returnRingHom_injective` | LANDED 69cfc53ff |
| `Dynamics/ReturnRingCrossedProduct` | `returnRingHom_surjective` (via ct-return-tower's `surjective_of_generators`, 2acee7950), `returnRingEquiv`, closed `returnRingCrossedProductStatement_holds` | LANDED 69cfc53ff; `#audit_closed_axioms` passes |

All four modules are queued in `wire-queue.txt`. ct-return-tower adds the census rows for tex 1723 and 1726.

Lean traps:
- On `ClopenCrossedProduct T k`, the field notation `x.coeff` resolves to the coefficient embedding
  `ClopenCrossedProduct.coeff`. Write `SkewMonoidAlgebra.coeff x g` for Laurent coefficients.
- `ReturnRingCrossedProductStatement` spells the corner at `coeff T k (charFn k hC.isClopen)`, while the return ring lemmas
  are stated at `ReturnCorner k hC` (`returnP`). `rw` cannot build a type-correct motive across them, so use `exact`, which
  checks definitional equality.
- `rw [h]` with `h : single g a = …` also rewrites inside a right-hand `coeff (single g a) 1`. Apply `coeff_single_apply` first.

## Notes for the owners (relayed through main)

- chain-core: keys `a1bda19b475a` and `8a557cb954fb` have no uniqueness or formal-powers lemma on origin. The module docstring asserts both by construction.
- hull-bridge:
  - Item 3 is a short composition of `IsLEFRing.matrix` with direct finiteness of finite rings. Its producer of `LEFStablyFiniteInterface` unblocks chain-reflection.
  - Item 4 composes `IsLEFRing.matrix` with `IsLEFRing.isLEF_units`.

## Conditional-baseline sweep (assigned by main 09-13 20:15, after the ~20:03 outage)

- CLAIM: rows before tex 1541 of `metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt` (census f78d19014).
  - Rule: wherever an `_of_*` theorem's binders are now all proved, turn it into a closed named endpoint along the printed
    route with `#audit_closed_axioms`, and flip its row.
  - Newly proved producers: ChainCoreClosures b09de1dcf, TransientMatricesClosed 6867e7460, ChainCoreModelsStatement
    a28419dba, CoreModelsLEF b7e521e57.
  - ms-core-4 takes tex 1541 onward.
  - Endpoints land in new `*Closed` modules; nobody else's modules are edited.
- Lane state at resume: every module in `ms-core-1.files` is landed with origin == local. The list is cleared, and no probes
  are pending.

### Sweep results (origin 096d9219c, census 0e622f840)

Register findings before tex 1541:
- 36 torsion-free findings (tex 66–303) wait on `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`, which has no producer. The
  chain-core closures do not touch them, so nothing is built.
- Tex 1321 `inlined-statement LeavittMFQuotientBothInclusions.elementary_le_commutator_of_trivial` gets a closed endpoint:
  `Manuscript/NonMFSentences/LeavittBothInclusionsClosed`, LANDED 141dfab7d (probe 0913-203527-46733 GREEN).
  - Declarations: `PrintedElementaryLeCommutator`, `printedElementaryLeCommutator_closed`.
  - The finding clears once the helper leaves leavitt-units' row (DROP below).

Partial census rows before tex 1541:
- LANDED `Manuscript/NonMFSentences/CoreRingReflectionProofClosed` and `ChainCoreItineraryClosed`, 348c26736 (probe
  0913-213440-42896 GREEN). Each endpoint has `#audit_closed_axioms`:
  - `printedCoreCornerMapKillsKernel` (tex 1534–1535), `printedCoreMatrixKillsKernel` (tex 1535–1536),
    `printedCoreMatrixQuotientLEF` (tex 1536–1537);
  - `printedItineraryIntersectionCycleCondition` (tex 1439–1441, `hcore` discharged by `cycleCondition_coreSubshift`).
- Census rows LANDED 04240efed: `f6962254d259`, `715cbd0f3410`, `30a44485e5e8`, `f2baa4a46f78`, `b180421b55ab`, `c99bf0bdb029`,
  `ded9e9646e4b`, `f7c8d8aab016` (all formalized over closed or origin-defined carriers).
- WITHDRAWN (09-14 ~00:10): `Manuscript/NonMFSentences/ChainCoreOpeningClosed` for key `d59fc0887768` (tex 1341). The
  coordinator reassigned the key to ct-rank-budget. The draft was never compiled: both probes failed on infrastructure (DNS, then
  MSI down). It is kept in the lane backup and offered to ct-rank-budget. It holds `one_notMem_coreTransientIdeal`, which says
  the defect ideal is proper, and `PrintedWholeRadicalProperDefectIdeal`.
- 19 DROP lines, in `overrides.tsv` form, are at `$NM/census/drop-lines-ms-core-1.tsv` and quoted in full in the message to
  ms-cite-2:
  - chain-reflection: 10 keys (1518–1527)
  - chain-itinerary: `2df08eeac3cb`, `c825bc73828a`
  - chain-subshift: `ded9e9646e4b`, `f7c8d8aab016`
  - hull-euler: `c99bf0bdb029`, `d8e1a694d87c`
  - ms-compress-1: `b180421b55ab`
  - ms-core-4: `f0c16e5c8519`
  - leavitt-units: `f6962254d259` (only `elementary_le_commutator_of_trivial`)
  - Every skipped row's key keeps a formalized row from a successor lane or from ms-core-1.
- Left as they are:
  - ms-inverses-3's five rows (tex 1489–1502): partial because the Lean proof takes a different route from the printed one, not
    because a binder is open.
  - About 25 keys are partial only through a root downgrade and restore once their carriers are wired: `ChainCoreClosures`,
    `CoreRingReflection`, `ChainCoreGeneralRecurrent`, `CoreSubshiftCycle`, `RetainedSubshiftPeriodic`, and ms-traces-3's
    modules.

## audit-nm-1 non-PASS rows (assigned by main 09-14, after the sweep)

- CLAIM: the five non-PASS rows of audit-nm-1 (report a0c769367). Their owners are down, so the fixes are additive: new modules
  only, no edits to other lanes' files. The rows go to ms-cite-2.
  1. `d4c878a7ac22`, thm:amenable-trace: add `Countable W` to `PrintedAmenableNonquasidiagonalTrace`, as a new named Prop and
     closed endpoint.
  2. `2a97fb901bad`, tex 284–286: a carrier along the printed route, via direct-limit permanence of MF.
  3. `c890294ad9b0`, tex 253–255: cite `ChainCoreClosures.printedCoreRingReflection_closed` for the first clause.
  4. `80279f06992b`, tex 292: the EL_n torsion clause over ℤ, via e₁₂(1)e₂₁(−1)e₁₂(1), of order 4.
  5. `2ff745dd7064`, tex 1060–1062: not MF for n ≥ 2, with nontriviality.
