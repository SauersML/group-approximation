# Lane `lix-coeff` — coefficient parameter: Relative*, RelHomotopy*, MV/excision/Künneth over K

Successor of `sp-coeff` and `sp-relhomotopy` (reports in this directory).  Clone `lix-k`.
Owns `CharClass/Coeff*`, `Relative*` (not RelativeSupport), `RelHomotopy*`, `CohomologyBasic*`,
`CohomologyAssoc*`, `CohomologyMayerVietoris*`, `CohomologyKunneth*`, `CohomologyLH*`
(`MayerVietoris*` and `CohomologyDelta*` went to lix-lh, 21:40).

## STEP 0 (2026-09-11 21:30 CDT)

Predecessor work is all on origin/main: `Coeff{AxiomCheck,Cohomology,Field,Leibniz,Line}`,
`RelHomotopy{Prism,Invariance}` are byte-identical to the shared tree (they show as untracked there
only because the shared index is stale), and every `attic/inflight/rescue-lix/…/Relative*.txt` copy
equals the compiled module landed at dd28464fc.  Nothing unlanded in this lane's prefixes.

## State of the scope at origin d3dc64fc4

* **Acyclicity over a field was already there**: `RelativeSmallChains.smallAnnComplexOf_acyclic (K) [Field K]`.
  The field is structural (dual of a quasi-iso is a quasi-iso because `K` is self-injective); over a
  general ring excision by this route fails.  Missing were its element form and the discharge of
  `LIXKRelMV.exists_relCocycle_split_of_acyclic`'s `hacyclic`.
* **Relative homotopy invariance over any `R` was already there**: `RelHomotopyInvariance`.
* **`RelativeLineHomotopy` use sites are all lix-oddside's** (`LIXHsq`, `LIXHsqLinear`,
  `LIXHsqNeighbourhood`); the generic replacement of `relPullback_eq_id_of_line` is
  `RelHomotopyIdentity.relPullback_eq_id_of_homotopy` fed the GL-path homotopy (their geometry).
* **F₂-only relative inputs of `LIXStepCOddRelative`**: ported additively in new `…Of` files (below).

## GREEN (compiled evidence)

Probe 0911-215900-88704, shared clone lix-b, base b42b3e553, SLURM 8 cpus, 12 modules rebuilt:
`RelHomotopyIdentity`, `RelativeSplitField`, `RelativeSubspaceIsoOf`, `RelativeProdContractibleOf`,
`RelativeLocalModelOf`, `CohomologyKunnethSplitOf`, `CohomologyKunnethSphereOf` — each with its own
`Built` line.  Landed 9d6fc7dbc (the other six were byte-identical on origin).  Not built:
`CohomologyKunnethHemiOf`, blocked by lix-lh's red `MayerVietorisPullOf` (166:6, 175:30, 165:54).

## AUTHORED, UNVERIFIED (landed unverified; first probe waits for clone lix-k)

| file | declarations | binder | landed |
|---|---|---|---|
| `RelativeSplitField` | `exists_smallAnnOf_preimage`, `LIXKRelMV.exists_relCocycle_splitOf` | `[Field K]` | 09bbb409d |
| `RelHomotopyIdentity` | `relPullback_eq_id_of_homotopy`, `relPullback_eq_id_of_contractible_param` | `[CommRing R]` | 09bbb409d |
| `RelativeSubspaceIsoOf` | `relPullback_bijective_of_absoluteOf` (five lemma), `relPullback_id_bijective_of_subspace_isoOf`, `absPull_eq_absPullOf` (rfl bridge) | `[CommRing K]` | 09bbb409d |
| `RelativeProdContractibleOf` | `relPullback_slice_bijectiveOf`, `relCohomologyProdIsoGenOf`, `relCohomologyProdIsoOf` | `[CommRing K]` | 09bbb409d |
| `RelativeLocalModelOf` | `localEquivOf`, `localGeneratorOf`, `eq_smul_localGeneratorOf`, `isUnit_localEquivOf_of_ne_zero`, `relCohomologyCongrPointOf`, `excisionIsoPointOf` | `[Field K]` | f54bd92fe (+ attic 652e20fcc) |
| `CohomologyKunnethSplitOf` | `knSigmaOf`, `kunneth_fst_eq_zeroOf`, `kunnethMap_naturalOf`, `kunnethMapOf`, `KunnethSecondInjectiveOf`, `kunnethInjective_of_secondOf`, `prodSwapEquivOf` | `[Field K]` / `[CommRing K]` | 91bd59ea4 |
| `CohomologyKunnethSphereOf` | `isZero_of_linearEquivOf`, `isZero_mvAmbientOf`, `prodOpenCohEquivOf`, `cohProdContractibleOf`, `isZero_prodOpen_of_contractibleOf`, `isZero_cohomology_of_isEmptyOf`, `isZero_prod_bandOf`, `isZero_prod_sphere_succOf`, `sphereCohSuspensionOf` | `[Field K]` / `[CommRing K]` | 1c3905806 |
| `CohomologyKunnethHemiOf` | `cohPullbackK_apply_eq`, `KnHemi.exists_pull_prSub_hemi{U,V}Of`, `mvResW{U,V}Of_pull_prSub`, `exists_pull_prSub_of_resOf`, `bandPullEquivOf`, `pull_bandHE_injectiveOf`, `pull_bandHE_knPr{Y,S}Of` | `[CommRing K]` | 1c3905806 |
| (handed to lix-cupone 22:05) `CohomologyLHDegreewiseOf` | `KnHemi.pull_cohCastOf`, `LHCast.lhDomainEquivOf`, `lhMap_eq_sum_lhTermOf`, `bijective_sum_lhTerm_of_gradedOf`, `bijective_sum_lhTerm_topOf`, `lhDomainEquiv2Of`, `lhMap_eq_sum_lhTerm2Of`, `bijective_sum_lhTerm_of_cardOf`, `pull_lhTermOf`, `bijective_pull_of_gradedOf`, `absToSub_surjective_of_gradedOf` | `[CommRing K]` | 32551de64 |

Rule 20 (21:45): shared clone lix-b, one batched probe of changed modules only, NM_CPUS 8, no watchers.
Probe 0911-214530 died at the msi hop while lix-b was PREP_PENDING (no job left); re-probe of the first
eight modules launched 21:58 (b5jnhi8lx).  `CohomologyLHDegreewiseOf` goes into the next batch.

Probe plan once lix-k exists (one small closure first): (1) `RelHomotopyIdentity`; (2) `RelativeSplitField`;
(3) `RelativeSubspaceIsoOf` + `RelativeProdContractibleOf`; (4) `RelativeLocalModelOf` + `CohomologyKunnethSplitOf`
(their closures reach lix-cupone's unverified `KroneckerSphere`).

`localEquivOf (ZMod 2)` is not definitionally `localEquiv`: the sphere iso over `K` is `LinearEquiv.ofFinrankEq`.

| `CohomologyKunnethStepOf` | `pull_sInclusion_knPrYOf`, `pull_knSlice_knPrS{,_const}Of`, `sphereNextOf`, `KnGenOf`, `knGen_of_injectiveOf`, `knGenOf_smul` | `[Field K]` | dcdfecefa |
| `CohomologyKunnethZeroOf` | `exists_zeroGenOf`, `zeroGenOf`, `mvRes{U,V}Of_zeroGenOf`, `pull_const_zeroGen_{pos,neg}Of`, `knGen_zeroGenOf` | `[Field K]` | dcdfecefa |

| `CohomologyKunnethStepDeltaOf` | `injective_sphereNextOf` (over lix-lh's `MVDelta.mvDeltaOf_naturality`, `MVDelta.mvDeltaOf_cup`) | `[Field K]` | 190c7a03f |
| `CohomologyKunnethInjectiveOf` | `one_ne_zero_unitOf`, `sphereGenOf`, `knGen_sphereGenOf`, `ne_zero_of_knGenOf`, `knGen_sphereTopClassOf`, `kunnethSecondInjectiveOf`, `kunnethInjectiveOf` | `[Field K]` | 190c7a03f |

Next probe (one batch, when lix-lh's `MayerVietorisPullOf` compiles): `CohomologyKunnethHemiOf`, `StepOf`,
`ZeroOf`, `StepDeltaOf`, `InjectiveOf`.

## NEEDS

* lix-lh: a compiled sha for `MayerVietorisPullOf` (red at b5f0dee2f: 166:6, 175:30, 165:54) and for
  `CohomologyDeltaNaturalOf` / `CohomologyDeltaCupOf` (landed unverified b7f9acbdf / 447d9146f).
* Then Surj*/Decomp over K: three `add_self_eq_zero_two` sites become `sub_self`/`sub_eq_zero`, and
  `MVDelta.mvDeltaOf_spec` carries `aU| − aV| = α`.

## TRAPS

* `git grep -E` has no `\b`: a pattern with `\b` silently matches nothing.  Use `git grep -nw`.
* Inside `namespace KnHemi` the F₂ `KnHemi.cohCast_zero` shadows the generic `CharClass.cohCast_zero`
  (innermost namespace wins): write `CharClass.cohCast_zero` in K-generic KnHemi files.
* From inside the lead's own process, SendMessage to "nonsofic-existence-41" is refused as self; use "main".
