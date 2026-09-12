# `lix-oddside-n` — the `k`-zero Step C at general rank `n` (successor of `sp-oddside-n`)

Lane of `notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, launched 2026-09-11 ~21:20 CDT by the lead
(nonsofic-existence-41). Clone `lix-d` (hard-link warmed from cs-endpoint by `nm/lixclone2`).
Owns `GroupApproximation/CharClass/LIXKGen*.lean`. Namespace `GroupApproximation.CharClass.KGen`.

**Deliverable (lead ruling 21:35):** for every stage `j` and every exponent `k` with `p ∤ k`, the
Step C half of `LIX.Gen.LemmaTwoFor n (lixDD n j) (KGen.bVecK n (k-1))`, i.e. the degree-`k`
section with `k` zeros. The names `psiVec` / `bVecK` / `normSq_psiVec` / `bVecK_normSq` stay.

## STEP 0 (21:25)

The predecessor's four files A–D (`LIXKGenSphere`, `LIXKGenPunctured`, `LIXKGenMap`,
`LIXKGenSection`) are on origin/main byte-identical to the shared tree, and compiled per rescue-lix's
gates. There is no unlanded predecessor work under `LIXKGen*` and no `attic/inflight` copy.

## GREEN

Nothing new yet (clone lix-d still PREP_PENDING at 21:29).

## AUTHORED, UNVERIFIED

| file | contents | landed |
|---|---|---|
| `LIXKGenSect` | `kSect k j w = ‖w‖·exp(i(arg(−w)+π+2πj)/(k+1))`; `kSect_pow` (`κ^{k+1} = ‖w‖^k w`), **`joinC_kSect` for every `w`** (no half-plane hypothesis: `‖x‖exp(arg x·i) = x` at every `x`), `kSect_neg_one = kRoot k j`, `norm_kSect`, `continuousAt_kSect`/`continuousOn_kSect` off the positive ray | 69b2bd332 (unverified) |
| `LIXKGenChart` | `ChartBase n = ℝ × (Fin n → ℂ)`, `ChartSrc n`, `chartQ`, `chartWeight`, **`sphereChartVec n (c,v) = Fin.cons (c·i − √(1−q)) v`**, `sphereChartVec_zero = −eZero n`, `_mem`, continuity; **`eulerLinearModel n`** with explicit inverse, `eulerContinuousLinearEquiv n`; `trivialBlockChart n`, `_eq_zero_iff`, `_zero` | 48f2ff1de (fix in attic e13a30f39) |
| `LIXKGenDeriv` | `chartLinearCLM n`, `sphereChartVec_eq`, `hasStrictFDerivAt_normSq_comp` (generic), `hasStrictFDerivAt_chartQ/chartWeight/sphereChartVec`, **`hasStrictFDerivAt_trivialBlockChart n`** | 48f2ff1de (fix in attic e13a30f39) |
| `LIXKGenLocalHomeo` | **`eulerLocalHomeo n`** (inverse function theorem), source/target/zero lemmas, **`lixChartPairHomeo n`**, **`lixLocalRelIso n m`**, `injective_lixLocalRelIso` | 48f2ff1de |
| `LIXKGenSectInverse` | `kZeroAngle`, `exp_kZeroAngle = kRoot`, `joinC_polar`, `arg_neg_joinC_polar_zero = (k+1)t`, **`kSect_joinC_polar`** | cca8b3156 |
| `LIXKGenSector` | `kRotBack`, **`kSector k j`** (open), `polar_of_mem_kSector`, **`kSect_joinC_of_mem_kSector`**, `neg_joinC_mem_slitPlane_of_mem_kSector`, `kSect_mem_kSector` | 43a160311 |
| `LIXKGenBundle` | rank-`n` `lixN`, `lixBundle`, `rank_lixBundle`, `lixTotalPair`, `lixPuncturedInTotal`, `lixKSectionTotal(_mapsTo)`, `lixKSRel`, `lixKS`, `lixPi`, `lixHE`, `lixJE`, `lixKSAbs`, `lixPiStar`, `lixKJ`, `lixKJloc`, `lixKI`, `lixK_hexact`, `lixKRho`, **`lixK_hcompat`, `lixK_hnat`, `lixK_hsection`** | a92331829 |
| `LIXKGenStepCWired` | **`puncturedAcyclic_lixKZero`** (discharged at every rank), `lixK_topClass_ne_zero` (naturality form), **`lixK_topClass_ne_zero_two`** and `_two_odd` (mod 2, local data at every zero) | a92331829 |
| `LIXKGenChartZero` | **`chartZeroVec n k j`**, **`psiVec_chartZeroVec`** (no hypothesis), `chartZeroVec_zero = kZeroVec`, `_mem`, **`trivialBlockK_chartZeroVec`** (one local model at every zero), `chartZeroVec_zero_mem_kSector`, `continuousOn_chartZeroVec` | c3be9d45d |
| `LIXKGenSphereChartHomeo` | clamp, `sphereLowerZero`, `sphereChartInv`, `one_sub_chartQ_inv`, **`sphereChartHomeo n`**, `sphereChartHomeo_zero = negEZero n` | 33531de45 |
| `LIXKGenZeroChartHomeo` | `psiSphere`, `sphereNearZero` (open), **`zeroChartHomeo n k j`** (inverse `Ψ_k` then the chart at `−e₀`), `psiSphere_zeroChartFun`, `zeroChartHomeo_zero = kZero n k j` | fb298522c |

## Model tests (on MSI acn112, scripts in `nm/lixoddn/`)

* `ksect_modeltest.py`: 315 checks, 0 failures. S1 `joinC k ∘ κ_j = id` on all of `ℂ` (worst
  `3.8e−14`, `k ≤ 8`); S2 `κ_j(−1) = kRoot`; S3 modulus; S4 `κ_j ∘ joinC k = id` on the open sector
  of half-width `π/(k+1)`; S4b fails outside it (load-bearing); S5 continuity off the positive
  ray; S6 `joinC k` maps the sector into the continuity domain.
* `chart_n_modeltest.py`: 30 checks, 0 failures, `n ≤ 5`. C1 centre, C2 on the sphere, C4 the
  Jacobian of the trivial block at `0` is `eulerLinearModel n` (central differences), C5 the
  inverse, C6 no stray zero near the origin.

## PLAN (remaining, in order)

1. `LIXKGenSectInverse`: `κ_j (joinC k z) = z` on the open sector (S4). With `joinC_kSect` this
   makes `x ↦ update x 0 (κ_j (x 0))` a homeomorphism of a neighbourhood of `−e₀` onto a
   neighbourhood of the `j`-th zero `kZeroVec n k j`, with `psiVec n k` as its inverse.
2. `LIXKGenChartZero`: the chart at the `j`-th zero and `psiVec n k ∘ chart_j = sphereChartVec n`
   on the chart domain, so the `k`-section read in `chart_j` is `trivialBlockChart n` at every `j`.
3. The rank-`n` bundle side (the rank-`n` analogue of `LIXHsq*` / `LIXResFibre` / `LIXHclass`, and the
   pair/mapping-torus vocabulary over `Gen.baseM n dd`) — **NEEDS an owner ruling**: `LIXBundleModel`,
   `LIXBundlePair`, `RelativeSupport`, and `LemmaTwoTopClass` are rank-two and outside `LIXKGen*`.
4. `LIXKGenStepCWired`: the rank-`n` counterpart of `LIXKStepCWired` through
   `topChernClass_ne_zero_kzero_two` (p = 2) at the `k` zeros of `bVecK n (k-1)`.

## NEEDS

* **lead:** who owns the rank-`n` bundle vocabulary (`lixN n dd`, `lixBundle` over `Gen.baseM n dd`,
  `lixTotalPair`, `RelativeSupport.lixJE/lixPiStar/lixHE` at rank `n`)? I propose creating
  `CharClass/LIXKGenBundle*.lean` myself (namespace `KGen`) unless lix-tower or lix-thom already
  has them.

## TRAPS

* `κ_j`'s forward identity `joinC k ∘ κ_j = id` needs no hypothesis at all, not even
  `Re w < 0`. The half-plane / sector hypothesis is load-bearing only for the inverse
  `κ_j ∘ joinC k = id`, which is what the openness of the chart's image needs.
