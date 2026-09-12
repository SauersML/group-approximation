# lx-kunneth — the Künneth objects of the rank-`n` LIX base (successor of lix-coeff's relaunch target)

Lane of the LIX STRONGEST swarm (lead nonsofic-existence-39, 2026-09-12).  Clone `lix-c` (shared with
lx-slice2).  Owns `CharClass/CohomologyKunneth*`, `Coeff*`, `Relative*` (not RelativeSupport),
`RelHomotopy*`, `CohomologyBasic*`, `CohomologyAssoc*`, `CohomologyLH*`, `Cup*`, `SteenrodCupOne*`,
`Kronecker*`, `CohomologySphere*`, `CohomologyContractible*`, `CohomologyTotal*`.

## GREEN

| probe | modules | state |
|---|---|---|
| 0912-102321-27141 (lix-c, SLURM acn67, base f29a035ec, 9207 jobs, PROBE GREEN) | `CharClass/CohomologyKunnethTorusN` (BUILT), `CharClass/CohomologyKunnethLixN` (BUILT) | on main since f29a035ec, bytes = green record |

Declarations (mod 2, F₂ Künneth layer, no `…Of` at `ZMod 2`):
* `KnTwo.sig1N`, `sigOddN`, `tx_inj_degreeN`, `tx_injN`, `decomp_evenN`, `decomp_even_lowN`, `totalSplitN`
  over the coefficient-free model `KnTwo.torusBaseOf Y n = (Y × S^{2n+1}) × S¹`.
* `KnLix.torusHomeo n dd`, `lixIso n dd : KGen.lixN n dd ≅ TopCat.of (KnTwo.torusBaseOf (baseY dd) n)`,
  `prY`, `prS1`, `prSodd := (lixIso n dd).hom ≫ KnTwo.prYOf/prS1Of/prSoddOf (baseY dd) n`.
* `KnLix.tx_inj n dd` — the `WuStepDData` field verbatim at `σ₁ = sphereTopClass 1 _`,
  `σodd = sphereTopClass (2n+1) _`.
* `KnLix.chern_split`, `KnLix.gamma_split_of_graded` (∃ a b, gamma_eq ∧ sq_b), `KnLix.gamma_split_mappingTorus`.

## AUTHORED, UNVERIFIED

* `CharClass/CohomologyKunnethLixNOf.lean` (over a field K): `KnCP.eq_zero_odd_prod_CP_succOf`,
  `noOddCohomology_prod_CPOf`, `noOddCohomologyOf_of_homeomorph`, `noOddCohomology_piCPOf`,
  `noOddCohomology_baseYOf`; `KnTwo.decomp_even_topOfK`, `decomp_even_lowOfK`, `totalSplitOfK`;
  `KnLix.map_hom_prYOfK`, `map_hom_zClassOfK`, `evenKunnethSplitOf` (lx-bundleP's `Gen.EvenKunnethSplitOf`
  body verbatim), `slice`, `slice_comp_prY`, `slice_comp_prS1`, `slice_map_prY_map`, `slice_map_zClass`.

## NEEDS

* none.

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
