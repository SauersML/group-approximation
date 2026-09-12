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

## AUTHORED, UNVERIFIED

`LIXKGenStepCHalf` has a probe running (the glue compiled, lix-evenside-n probe 0911-221342-93884). It contains:

- `KZeroStepCData`, which keeps only `u`, `xloc`, `hsplit`, `hx` and `hclass`;
- `stepCHalf_two_of_kZeroStepCData`;
- `stepCHalf_two_powers`, covering every stage `j` and every odd `e`, at `bVecK n (e−1)`.

This module reshapes the remaining leaves into StepCHalf's form; it does not discharge them.

## Model tests (MSI acn112, scripts in `nm/lixoddn/`)

- `ksect_modeltest.py`: 315 checks, 0 failures.
- `chart_n_modeltest.py`: 30 checks, 0 failures, for `n ≤ 5`.

## REMAINING LEAVES at `p = 2`

The remaining leaves are the fields of `KZeroStepCData`:

- **(3) `hx i`** (lix-oddside): every local class is nonzero.
- **(4) `hsplit`** (lix-oddside): relative Mayer–Vietoris over the `k+1` punctures.
- **(5) `hclass`** (this lane): `jE u = π^* γ_r`, the rank-`n` counterpart of `LIXHclass`.
  - The Thom stack `ThomChartTautZero`, `ThomBridgeRelToAbs` and most of `LIXThomClassTerm` are generic in the `Bundle`.
  - What is rank-specific: `lixThomClassTerm`, `lixLHplus`/`lixLHhyper`, `lixChern`, `lixChern_top_eq_gamma`, `thomJmTotal_lixThomClassTerm` and `lixHclass`.
  - Plan: add `LIXKGenThomTerm`, `LIXKGenChern` and `LIXKGenHclass` over `KGen.lixBundle n`, coordinated with lix-thom (`ThomDataOf`/`ThomHabsOf`) and lix-lh (`ChernClassesOf`).
- **The top class:** `topClass` in StepCHalf is still a parameter. The glue's `lemmaTwoFor_powers_of_stepC_modP` uses `γfun j W r` in some `H j`, so an adapter from `cohomologyZMod2 (lixN n dd) (2r)` to `TotalH` is needed.

## TRAPS

- **Linters:**
  - `field_simp; ring` can fail with "No goals" because `field_simp` sometimes closes the goal. When the identity is polynomial in `c⁻¹`, use `push_cast; ring`. When it needs `c ≠ 0`, use `div_mul_cancel₀`.
  - `simp only [..] <;> ring`, when simp leaves a single goal, is a seq-focus linter ERROR under warningAsError. Put `ring` on the next line.
  - An unused lambda binder (`fun w => ...`) is an error. Write `fun _ =>`.
- **Elaboration:**
  - `ContinuousAt.comp hg hf` can unify `f x` against an applied term the wrong way, e.g. `sphereChartVec n w 0` read as `f := sphereChartVec n w`, `x := 0`. Pin it with `(f := fun v => ...)`.
  - `∑ j, ‖z j.succ‖^2` inside `show` does not know `j`'s type. Write `∑ j : Fin n, ...`.
  - `cohomologyZMod2` lives in `ThirdParty.HamSandwich.SphereOddDegree`, so open that namespace.
- **Maths:** `joinC k ∘ κ_j = id` needs no hypothesis, because `‖x‖ exp(i arg x) = x` holds even at `0`. Only the inverse composite, and hence the openness of the chart's image, needs the sector.
