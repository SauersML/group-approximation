# Lane `lix-cupone` — signed cup-1 over `K`, and the Kronecker/UCT + sphere port over a field

Successor of `sp-cupone` (report `notes/lix-stronger-lane-reports/sp-cupone.md`, read in full).
Clone `lix-l`.  Owns `CharClass/CupOne*`, `SteenrodCupOne*`, `Kronecker*`, `CohomologySphere*` and
`CohomologyContractible*`.

## STEP 0 (2026-09-11 ~21:30)

Every predecessor file is on origin, byte-identical to the shared tree: `CupOneSign`, `CupOneCochain`,
`CupOneInsert`, `CupOneCoboundary`, `CupOneComm`, `CupOneAxiomCheck`, `KroneckerClassifier`,
`KroneckerMap`, `KroneckerEquiv`, `KroneckerContractible`.  Nothing is unlanded and there is nothing in
the attic.  rescue-lix's compiled records cover `KroneckerEquiv` and `KroneckerContractible`.  The six
`CupOne*` files and `KroneckerClassifier`/`KroneckerMap` were green on thm-e on 09-10 and have not been
re-verified at the current tip; they are in this lane's overlay so the first probe records evidence.

## GREEN

Probe 0911-215042-37708 (clone lix-d, acn112, base 2e9a9873e): `BUILT KroneckerSphereHomology`,
`BUILT KroneckerSphere`, both COMPILED, first probe.  Landed normally at 19c641d25.  The table below
records their contents.

Probe 0911-215835-86270 (lix-d, base d0f2cc746, 2073 jobs, PROBE GREEN): `BUILT CupOneTotal`;
`evenClassesCommute` depends on `[propext, Classical.choice, Quot.sound]`.  Landed normally at 75844be91.
Scope (1)–(3) of sp-cupone is now compiled on main: the signed cup-1 layer (09-10), the Kronecker/UCT and
sphere port over a field, and `TotalHOf.IsEven` / `mul_comm_of_isEven_left/_right`.

## AUTHORED, UNVERIFIED (landed per rule 18)

| file | contents | landed |
|---|---|---|
| `CharClass/KroneckerSphereHomology.lean` | over `K`: `isZero_subChainComplex_homologyOf_of_contractible`, `sphereSuspensionOf`, `sphereHomologyOf_isZero_of_gt/_lt/_ne`, `mvF0Of_injective`, `mvX3_H1_isZeroOf`, `sphereH1Of_isZero`; base case over a field `h0_sphere0Of_finrank`, `H0augOf_surjective`, `reducedH0_sphere0_isoOf`, `kerBand_isoOf`, `kerF0_iso_kerBandOf`, `sphereH1_iso_kerF0Of`, `sphereOneIsoOf : H₁(S¹;K) ≅ K`; `sphereTopIsoOf : Hₙ(Sⁿ;K) ≅ K`; closed `sphereHomologyOverField` | d244e90db (+ edit) |
| `CharClass/KroneckerSphere.lean` | dualised through `kroneckerEquivOf`: `sphere_coh_isZero_of_gtOf/_ltOf/_neOf`, `sphere_coh_top_finrankOf`, `sphereTopEquivOf`, `sphereTopClassOf(_ne_zero)`, `sphere_coh_top_eq_smulOf`, `cohZero_finrankOf`, `cohZeroEquivOf`, `sphereCohZeroEquivOf`, `cohZeroEquivOfContractibleOf`, `ZMod 2` restatements; closed `sphereCohomologyOverField` | d244e90db (+ edit) |

Method, as in sp-cupone §4.4: no vendored or existing CharClass file is edited.  Every `ZMod 2` in the
vendored sphere files (`SphereModTwoHomologyVanishing`, `…AboveDimension`, `SphereModTwoOneBase`,
`SphereModTwoTopClass`, `SphereTopCohomologyRankOne`) instantiates a generic construction
(`subChainComplex R`, `mvShortComplex R`, `mvHomologyIso_succ R`, `homologyIsoOfHomotopyEquivModule R`,
`H0Gen.H0aug R`, `smallChains_homologyIso R`), so the twins substitute `K`.  `[Field K]` enters only at
the rank count of reduced `H₀(S⁰; K)` and, in cohomology, through `kroneckerEquivOf` and
`Subspace.dual_finrank_eq`.

| `CharClass/CupOneTotal.lean` | over lix-lh's `TotalHOf K X` (`ChernTotalRingOf`, itself unverified): `TotalHOf.IsEven`, `isEven_zero/_one/_of`, `IsEven.add/.mul/.map`, `of_cohCast`, `component_of_ne`, `sum_support_of'`, `commute_of_of_even_left`, `commute_of_even_left` (a homogeneous even class commutes with every element), `mul_comm_of_isEven_left/_right`; closed `evenClassesCommute` | this batch |

## NEEDS

- Clone `lix-l` (lixclone2, started 21:19; 8 of 12 clone directories exist at ~21:55).

## TRAPS

- `even_zero` does not exist at the pin: `Even (0 : α)` is `Even.zero` (to_additive of `IsSquare.one`).

- A binder-shift hazard: proving `def P : Prop := ∀ (K : Type) [Field K] (n : ℕ), …` by
  `fun K _ n => …` relies on how the elaborator matches an explicit `_` against an instance-implicit
  expected binder.  Prove such endpoints with `intro K _ n` instead.

## Scope 2 (2026-09-11 evening): lix-steenrod's block OddPAcyclic* (plan §3.4 route (A)) — COMPILED

| file | contents | evidence |
|---|---|---|
| `OddPAcyclicAlgebra` | ring algebra: recursive contraction `contrOp`, `eAll`; `sum_mul_contrOp_add` (`d S + S d = 1 − eAll E` from five slot relations); `eAll_eq_zero`, `contrOp_mem` | 0911-232214-2678 |
| `OddPAcyclicSimplex` | signed exactness of `singFreeR K` on Δⁿ over any CommRing: `free K ≅ sigmaConst K` by `Adjunction.leftAdjointUniq`, `alternatingFaceMapComplex.mapIso`, homotopy invariance at `K`; no unsigned face sum; `printedSignedSimplexExact` | 0911-233328-58765, landed 8739ca3a8 |
| `OddPAcyclicTag` | `chainS`, `chainE` from the splitting; one-slot contraction and `∂e = 0`, `e∂ = 0` on tags | 0911-232214-2678 |
| `OddPAcyclicSlot` | generic `slotOp`, `slotS`, `slotE`, the five relations with input-prefix Koszul signs, `tupDAll_mul_contrOp_add` | 0911-232214-2678 |
| `OddPAcyclic` | grading, assembly; EXPORT `tupD_exists_preimage_stdSimplexTop`; `printedTupleAcyclicOnModels` | 0911-234129-25726, landed 9b8b95eee |
| `OddPAcyclicZero`, `OddPAcyclicZeroAug` | (E0) degree 0: `Sigma.desc lsingle` intertwines the signed differentials at 1→0, vendored `H0Gen.chainGenerator_sub_mem_range` transports; telescoping over slots; EXPORT `tupD_exists_preimage_zero_stdSimplexTop` against `tupAug`; `printedTupleAcyclicZeroOnModels` | 0912-001526-78604, landed c74ce78c3 |

Sign model test (`backup/lix-cupone/oddp_acyclic_signs.py`, acn112, seconds): chains of the 2-simplex, r = 1, 2, 3, two
contraction data, GREEN; negative control (unsigned slotS) fails the slot relations H1/H2 but not the composite
identity — the composite is sign-insensitive on its support, confirming §3.4(A).

## Scope 3 (2026-09-12): odd-p Chern layer inputs over K — COMPILED

| file | contents | evidence |
|---|---|---|
| `CupVanishRepOf` | K-twin of `CartanCoverRep`, `CupVanishSmallAnn`, `CupVanishCover`: `exists_cocycle_vanishing_onOf`, `exists_smallAnn_preimageOf`, `cocycleClassK_eq_zero_of_mem_smallAnnOf(_posOf)`, `cup_eq_zero_of_absToSub_eq_zeroOf`; closed `printedCupVanishTwoSet` | compiled line in 0912-003754-78332, landed 8f8fc1ab8 |
| `CupVanishIterateOf` | K-twin of `CupVanishSub`, `CupVanishIterate`: `pull_cup_eq_zero_of_supOf`, `eq_zero_of_pull_opIncl_topOf`, `pull_cup_eq_zero_of_eq_supOf`, `exists_prod_vanishing_on_coverSupOf`, `prod_eq_zero_of_coverOf` with the ORDERED `List` product (`TotalHOf K X` is not commutative); closed `printedCupVanishCover` | compiled line in 0912-003754-78332, landed 9b557a363 |
| `CohomologyTotalNontrivialOf` | `cocycleClassK_zero_injectiveOf`, `one_ne_zero_cohZeroOf`, `nontrivial_totalHOf` + instance; closed `printedCohomologyTotalNontrivial` | 0912-004700-28881 PROBE GREEN, landed 1e3038157 |

Probe 0912-003754-78332 exited rc=1.  Of its modules, only CohomologyTotalNontrivialOf has no compiled line,
and it was fixed at 1e3038157.  The bytes on main match every compiled md5 above.  The planned
`CupVanishCoverOf` and `CupVanishSubOf` are not separate files.  Their theorems are
`cup_eq_zero_of_absToSub_eq_zeroOf` (RepOf §3) and `pull_cup_eq_zero_of_supOf` (IterateOf), so separate
files would only duplicate declarations.  The `*Of` files add no new definitions: `opTopIso` and
`coverSup` carry no coefficients and are reused from `CupVanishIterate`.

Also compiled this session: `CohomologyLHDegreewiseOf` (lix-coeff's file, handed over), no edits needed.

## TRAPS (added)

- A CharClass-level `singularBoundary : SingularBoundaryData` shadows the vendored
  `AffineBarycentricSubdivision.singularBoundary`; qualify the vendored names.
- `rw [← Category.assoc]` across `singularChainGroup K X (0+1)` and the coproduct object is not type-correct at
  instances transparency; compare on a generator with `change` instead.
- `Set.range_coe_subtype` is `Subtype.range_coe_subtype` at the pin.
- `Finset.single_le_sum` needs `(f := …)` when the summand is a projection; `split_ifs` needs a `show` to beta-reduce a
  lambda-built tuple first.
- `TotalHOf K X` is a `DirectSum.GRing`, not a `CommRing`: `∏ l ∈ Finset.range r` does not typecheck; use
  `((List.range r).map f).prod` and `List.prod_range_succ`.
