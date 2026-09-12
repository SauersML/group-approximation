# `lix-oddside-n`: the `k`-zero Step C at general rank `n` (successor of `sp-oddside-n`)

This is a lane of `notes/LIX_STRONGER_PROGRAM_2026-09-10.md`. The lead (nonsofic-existence-41) launched it on 2026-09-11 at about 21:20 CDT. It probes on the shared clone `lix-a`, together with lix-tower and lix-powers.

- Owned files: `GroupApproximation/CharClass/LIXKGen*.lean`.
- Namespace: `GroupApproximation.CharClass.KGen`.

## Deliverable (lead rulings 21:35, 22:10, 22:45)

The deliverable is `Gen.StepCHalf n (LIX.Gen.lixDD n j) (KGen.bVecK n (e-1)) topClass` for every stage `j` and every exponent `e` with `p ∤ e`. It comes first at `p = 2`.

- The spelling is in `CharClass/LIXLemmaTwoGenGlue.lean`, owned by lix-evenside-n.
- lix-oddside owns leaves (3) `hx` and (4) `hsplit`, in `CharClass/LIXKGenLocal*`, written over this lane's names.
- This lane keeps leaves (1) `absLine`, (2) `exc`/`chartIso` and (5) `hclass`, plus the StepCHalf assembly.

## GREEN: compiled and landed normally

- **Probe 0911-220933-61809:** `LIXKGenSect`, `LIXKGenChart`, `LIXKGenDeriv`, `LIXKGenLocalHomeo`. Landed at 2749542ef.
- **Probe 0911-222214-52591:** `LIXKGenBundle`, `LIXKGenStepCWired`, `LIXKGenSectInverse`, `LIXKGenSector`. Landed at 93bb40412.
- **Probe 0911-224111-84100:** `LIXKGenChartZero`. Landed at 68780388f.
- **Probe 0911-225543-57885 (PROBE GREEN, 8929 jobs):** `LIXKGenSphereChartHomeo`, `LIXKGenZeroChartHomeo`, `LIXKGenBaseChart`, `LIXKGenTopLine`. Landed at 37af80afc; the other three were already byte-identical on main.

Main declarations, by module:

| module | main declarations |
|---|---|
| `LIXKGenSect` | `kSect`, **`joinC_kSect`** for every `w`, `kSect_neg_one = kRoot`, `continuousOn_kSect` |
| `LIXKGenSectInverse` / `LIXKGenSector` | `kSect_joinC_polar`, **`kSector`** (open), **`kSect_joinC_of_mem_kSector`**, `kSect_mem_kSector` |
| `LIXKGenChart` / `Deriv` / `LocalHomeo` | `sphereChartVec n`, `eulerLinearModel n`, **`hasStrictFDerivAt_trivialBlockChart n`**, **`eulerLocalHomeo n`**, `lixLocalRelIso n m` |
| `LIXKGenChartZero` | **`psiVec_chartZeroVec`** (no hypothesis), **`trivialBlockK_chartZeroVec`** (one local model at every zero) |
| `LIXKGenSphereChartHomeo` / `ZeroChartHomeo` | **`sphereChartHomeo n`**, **`zeroChartHomeo n k j`** (`zeroChartHomeo_zero = kZero n k j`) |
| `LIXKGenBundle` | rank-`n` `lixN`, `lixBundle`, `rank_lixBundle`, `lixTotalPair`, `lixPuncturedInTotal`, `lixKSRel`, `lixJE`, `lixKSAbs`, `lixPiStar`, `lixKJ`, `lixKJloc`, `lixKI`, `lixKRho`, `lixK_hexact`, `lixK_hcompat`, `lixK_hnat`, `lixK_hsection` |
| `LIXKGenStepCWired` | **`puncturedAcyclic_lixKZero`** (discharged at every rank), `lixK_topClass_ne_zero`, **`lixK_topClass_ne_zero_two`**, `_two_odd` |
| `LIXKGenBaseChart` | **`lixKRelModelIso n k dd i q`**: `H^q(N, N∖z_i) ≅ H^q(ℂ^r, ℂ^r∖0)`. This DISCHARGES leaf (2). |
| `LIXKGenTopLine` | **`absEquiv_lixN n dd hdd`**: `H^{2r}(N; F₂) ≃ F₂`. This DISCHARGES leaf (1). |

- **Probe 0911-231632-71904 (PROBE GREEN):** `LIXKGenStepCHalf`, landed at a9a92178b. It holds `KZeroStepCData` (`u`, `xloc`, `hsplit`, `hx`, `hclass`), `stepCHalf_two_of_kZeroStepCData` and `stepCHalf_two_powers`.

- **Probe 0911-235706-48216 (PROBE GREEN, 9269 jobs):** the four hclass modules below, landed at a0bc1306d (unverified) and 409347c6a (the `LIXKGenChern` fix).

## hclass at rank n (compiled)

| module | contents |
|---|---|
| `LIXKGenChern` | rank-`n` `LixFamily`, `LixChernDeg`, **`lixChern n dd`**, `lixChern_eq_of_rank`, `lixChern_mappingTorus`, **`lixChernOf n chern : TotalH (lixN n dd)`**, `lixChernOf_mappingTorus`; instances for `unitVectors (Fin (n+1))` |
| `LIXKGenThomTerm` | `lixTopCoeff n dd` (≠ 0), `lixLHplus n`, `lixLHhyper n`, **`lixThomClassTerm n hGc hGu`** (≠ 0), `thomJmTotal_lixThomClassTerm n`, `lixChern_top_eq_gamma n` |
| `LIXKGenHclass` | **`lixHclass n`**: `jE (lixThomClassTerm n) = π^* (lixChern n dd W _ _ r)`. This is LEAF (5). |
| `LIXKGenStepCHalfTop` | **`KZeroLocalData`** (only `xloc`, `hsplit`, `hx`, with `u := lixThomClassTerm n`), `kZeroStepCData_of_kZeroLocalData`, **`stepCHalf_two_lixChernOf`** and **`stepCHalf_two_powers_lixChernOf`** at `topClass := fun W => lixChernOf n (lixChern n dd) W ((∑ j, dd j) + (n + 1))`, the glue's `γfun` spelling |

## Local square at p = 2: this lane's half of the split with lix-oddside (2026-09-12)

lix-oddside owns `LIXKGenLocalEta`, `Linear`, `Homotopy`, `Legs`, `Square` and `Nonzero`. This lane owns the three files below. The convention is `(n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) {G} (hGc) (hGu)`, with `dd` explicit.

| module | state | main declarations |
|---|---|---|
| `LIXKGenLocalPair` | COMPILED (as an import in probe 0912-003310-54233), landed at 0f038ff96 | `otherZeros`, `lixKTrivSet` (trivSet ∩ otherZerosᶜ), **`lixKTrivBall`**, `lixKTrivBall_subset`, `_subset_target`, `isOpen_`, `lixKZero_mem_`, **`lixKZero_notMem_lixKTrivBall`**, `contractibleSpace_lixKTrivBall`, `lixKZeroInBall`, `lixKBundlePairIso`, `two_le_two_mul_lixRank`, **`lixKLocalPairIsoClosed`** |
| `LIXKGenLocalRes` | GREEN (probe 0912-003310-54233), landed at fee3cc504 | `lixKTotalInclOn_mapsTo`, **`lixKRes`**, **`lixKRes_lixThomClassTerm_ne_zero`** |
| `LIXKGenLocalNbhd` | landed UNVERIFIED at 416ff8bad; probe running | `lixKHsqRad` (cap `1/(n+2)`), **`lixKHsqBall`**, `lixKBC_image_lixKHsqBall_subset`, `_subset_bc_source`, `_subset_fc_source`, `zero_mem_`, `norm_lt_half_of_mem_`, `chartQ_lt_one_of_mem_`, `chartQ_le_one_of_mem_`, `circCoord_mem_Ioo_of_mem_`, **`smul_mem_lixKHsqBall`**, **`lixKU`**, `isOpen_lixKU`, `zero_mem_lixKU`, `lixKU_subset_target`, `symm_mem_lixKHsqBall`, **`lixKULine`**, `lixKShrinkMap`, `lixKShrink_mapsTo`, **`injective_lixKShrink`** |

One maths change from rank two: the cap is `1/(n+2)`, not `1/2`. `chartQ n` has `n + 1` squared terms, so a cap of `1/2` only gives `chartQ < (n+1)/4`. With `1/(n+2)` it gives `chartQ < (n+1)/(n+2)² < 1`.

## Model tests (MSI acn112, scripts in `nm/lixoddn/`)

- `ksect_modeltest.py`: 315 checks, 0 failures.
- `chart_n_modeltest.py`: 30 checks, 0 failures, for `n ≤ 5`.

## REMAINING LEAVES at `p = 2`

`KGen.KZeroLocalData n k dd hGc hGu hGe` holds all that is left of the Step C half at `p = 2`:

- **(3) `∀ i, xloc i ≠ 0`** (lix-oddside): every local class is nonzero.
- **(4) `LocalSplit (fun i => lixKRho n k dd i (2r)) ((lixKSRel n k hGc hGu hGe (2r)).hom (lixThomClassTerm n hGc hGu)) xloc`** (lix-oddside): relative Mayer–Vietoris over the `k+1` punctures.

Discharged by this lane: (1) `absEquiv_lixN`, (2) `lixKRelModelIso`, (5) `lixHclass`, and the `γfun` adapter. `stepCHalf_two_powers_lixChernOf` states the Step C half at `topClass := fun W => lixChernOf n (lixChern n (lixDD n j)) W ((∑ i, lixDD n j i) + (n + 1))`. Step D (lix-evenside-n, `stepDHalf_of_wu`) must use the same `γfun`, with `N := KGen.lixN n (lixDD n j)`.

## TRAPS

- **Instances:** a `show dite _ _ _ = _` over a classical `if h : ∃ …` needs `open scoped Classical in` on the THEOREM too, not only on the def.
- **Linters:**
  - `field_simp; ring` can fail with "No goals" because `field_simp` sometimes closes the goal. When the identity is polynomial in `c⁻¹`, use `push_cast; ring`. When it needs `c ≠ 0`, use `div_mul_cancel₀`.
  - `simp only [..] <;> ring`, when simp leaves a single goal, is a seq-focus linter ERROR under warningAsError. Put `ring` on the next line.
  - An unused lambda binder (`fun w => ...`) is an error. Write `fun _ =>`.
- **Elaboration:**
  - `ContinuousAt.comp hg hf` can unify `f x` against an applied term the wrong way, e.g. `sphereChartVec n w 0` read as `f := sphereChartVec n w`, `x := 0`. Pin it with `(f := fun v => ...)`.
  - `∑ j, ‖z j.succ‖^2` inside `show` does not know `j`'s type. Write `∑ j : Fin n, ...`.
  - `cohomologyZMod2` lives in `ThirdParty.HamSandwich.SphereOddDegree`, so open that namespace.
- **Maths:** `joinC k ∘ κ_j = id` needs no hypothesis, because `‖x‖ exp(i arg x) = x` holds even at `0`. Only the inverse composite, and hence the openness of the chart's image, needs the sector.
