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
