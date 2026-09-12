# lx-kunneth — the Künneth objects of the rank-`n` LIX base (successor of lix-coeff's relaunch target)

Lane of the LIX STRONGEST swarm (lead nonsofic-existence-39, 2026-09-12).  Clone `lix-c` (shared with
lx-slice2).  Owns `CharClass/CohomologyKunneth*`, `Coeff*`, `Relative*` (not RelativeSupport),
`RelHomotopy*`, `CohomologyBasic*`, `CohomologyAssoc*`, `CohomologyLH*`, `Cup*`, `SteenrodCupOne*`,
`Kronecker*`, `CohomologySphere*`, `CohomologyContractible*`, `CohomologyTotal*`.

## GREEN

| probe | modules | state |
|---|---|---|
| 0912-102321-27141 (lix-c, SLURM acn67, base f29a035ec, 9207 jobs, PROBE GREEN) | `CharClass/CohomologyKunnethTorusN` (BUILT), `CharClass/CohomologyKunnethLixN` (BUILT) | on main since f29a035ec, bytes = green record |
| 0912-105131-84638 (lix-c, acn112 64-71, base 8c49e4396, 9238 jobs, PROBE GREEN) | `CharClass/CohomologyKunnethLixNOf` (BUILT) | on main since 8c49e4396, bytes = green record |

Declarations (mod 2, F₂ Künneth layer, no `…Of` at `ZMod 2`):
* `KnTwo.sig1N`, `sigOddN`, `tx_inj_degreeN`, `tx_injN`, `decomp_evenN`, `decomp_even_lowN`, `totalSplitN`
  over the coefficient-free model `KnTwo.torusBaseOf Y n = (Y × S^{2n+1}) × S¹`.
* `KnLix.torusHomeo n dd`, `lixIso n dd : KGen.lixN n dd ≅ TopCat.of (KnTwo.torusBaseOf (baseY dd) n)`,
  `prY`, `prS1`, `prSodd := (lixIso n dd).hom ≫ KnTwo.prYOf/prS1Of/prSoddOf (baseY dd) n`.
* `KnLix.tx_inj n dd` — the `WuStepDData` field verbatim at `σ₁ = sphereTopClass 1 _`,
  `σodd = sphereTopClass (2n+1) _`.
* `KnLix.chern_split`, `KnLix.gamma_split_of_graded` (∃ a b, gamma_eq ∧ sq_b), `KnLix.gamma_split_mappingTorus`.

## AUTHORED, UNVERIFIED

* none.  COMPILED since: `CharClass/ThomLIXHclassOf.lean` (split item S1 of lx-stepcK-agree, landed 4b11d2f74; probe
  0912-115747-11347, acn112 64-71, base 21c8eb2a6, 9218 jobs, PROBE GREEN, BUILT, axioms propext/choice/Quot.sound): over any
  CommRing `gammaCoeff_eq_of_valOf`, `gamma_top_eq_chernCoeffOf`, `chernMul_top_unitOf`, `lhTerm_zero_classOf`,
  `lhTerm_at_index_zeroOf`, `pull_bridgeChartIncl_lhSumOf` (ξ arbitrary + `hξ : pull (cmap (bridgeChartIncl p)) 2 ξ = 0`);
  over a field `relToAbs_bridgeTotalOf_eq_lhSumOf`, `relToAbs_total_eq_pull_coordOf` (jE u = π^* of the zeroth Thom
  coordinate).  Consumers: lx-sliceK (S2 `LIXKGenOfStepCThom`), lx-stepcK-local.

Compiled over a field K (`CharClass/CohomologyKunnethLixNOf.lean`): `KnCP.eq_zero_odd_prod_CP_succOf`,
  `noOddCohomology_prod_CPOf`, `noOddCohomologyOf_of_homeomorph`, `noOddCohomology_piCPOf`,
  `noOddCohomology_baseYOf`; `KnTwo.decomp_even_topOfK`, `decomp_even_lowOfK`, `totalSplitOfK`;
  `KnLix.map_hom_prYOfK`, `map_hom_zClassOfK`, `evenKunnethSplitOf` (lx-bundleP's `Gen.EvenKunnethSplitOf`
  body verbatim), `slice`, `slice_comp_prY`, `slice_comp_prS1`, `slice_map_prY_map`, `slice_map_zClass`.

## NEEDS

* none.

## SPLIT (independent helper tasks)

* none open: the Künneth side of `WuStepDData` (mod 2) and of `RealBundleModP` / `RealTorusModP` (over K) is
  authored; what remains is compile evidence for `CohomologyKunnethLixNOf` (probe running).

## CONSUMERS (spellings agreed)

* lx-slice2 (`Gen.wuStepDData_lixN`): `KnLix.prY/prS1/prSodd`, `KnLix.tx_inj`, `KnLix.gamma_split_of_graded`.
* lx-torusP (`Gen.realTorusModP_ofIso`): `KnLix.lixIso` and the three projections, definitionally composites.
* lx-bundleP (`Gen.realBundleModP_stages`): `KnLix.evenKunnethSplitOf K n dd`, `KnLix.slice` + two lemmas.
* lx-endpoint: identical map spellings in F₂ and K; σ over K = `sphereTopClassOf K 1 _`, `sphereTopClassOf K (2n+1) _`.

## TRAPS

* `TotalH.of_mul` (F₂, `SteenrodTotal`/`ChernTotalRing`) and `TotalHOf.of_mul` (K, `ChernTotalRingOf`) point in
  OPPOSITE directions: the K lemma is `of K X (m + n) (cup a b) = of K X m a * of K X n b`.  Check the
  statement before choosing `←`; the F₂ green used the forward form on products.
* zsh `"$B:path"` colon modifier: write `"${B}:path"`.
