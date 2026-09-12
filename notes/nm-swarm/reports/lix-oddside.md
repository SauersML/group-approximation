# `lix-oddside` — Step C with `k` zeros (successor of `sp-oddside`)

Launched 2026-09-11 ~21:30 CDT by the lead. Owns `CharClass/LIXK*` except `LIXKGen*`, plus
`LIXSection*`, `LIXHsq*`, `LIXStepCOdd*`. Clone: `lix-b` (shared with lix-coeff and lix-thom, rule 20).

## STEP 0 (21:40)

Every file under my prefixes on disk equals origin/main; the predecessor's eight `LIXK*` files are on
main and compiled in rescue-lix's gates (green records 0911-191258, 0911-194230). No unlanded
predecessor work and no attic copy.

## Index convention (fleet ruling 21:35)

Internal index `k` ↔ `k + 1` zeros (`joinC k` has degree `k + 1`). The Lemma 2 section of exponent `e`
is `bVecK (e − 1)`; the adapter is `lixK_topChern_ne_zero_exponent (e) (he : 1 ≤ e) (hodd : Odd e)`.

## AUTHORED, LANDED UNVERIFIED (probe bsu1ew2by running)

| file | contents | sha |
|---|---|---|
| `LIXKLocalSplit` | relative cocycle-class API (`relCocycleClass`, `_surjective`, `_add`, `relPullback_id_relCocycleClass`, `relCohomology_eq_zero_of_forall_mem`); two-set split on classes `exists_relClass_split_of_acyclic`; finite-puncture induction `exists_localSplit_of_acyclic` over any `CommRing`; `exists_localSplit_two` (the `LocalSplit` obligation at `ZMod 2`, unconditional) | fdc38fd6f |
| `LIXKLocalRestrict` | `restrictTo`; `restrictTo_relPullback_id_eq_zero` (a piece away from `B` restricts to 0 through `Hⁿ(B,B)=0`); `xloc_ne_zero_of_restrictTo_ne_zero`; `topChernClass_ne_zero_kzero_two_of_restrict` (generic `N`, no split hypothesis) | 9aac20358 |
| `LIXKStepCExponent` | `kSwapHomeo` (unitary `S⁵` map `−e₃ ↦ ζⱼe₁`), `lixKSwap`, `lixKExc`; `KLocalNonzero` (the one remaining field); `lixK_topChern_ne_zero_of_localNonzero` (split, agreement, acyclicity, line data, Thom class all closed); `lixK_topChern_ne_zero_exponent` | c7f8926dc |

## Residual (exact)

`KLocalNonzero k hGc hGu hGe`: for each zero `z_i` a set `B ∌ z_j (j ≠ i)` with
`restrictTo B (lixKSRel k … u) ≠ 0`, `u = lixThomClassTerm hGc hGu`. It is the one-zero local
computation (`lixHsq` + `injective_lixRes` + `lixThomClassTerm_ne_zero`) run at `z_i` for the section
`(e₁, Ψ_k x)`. The existing chain is pinned at `−e₃` with `b = x`.

## PLAN

1. Probe the three files; fix and land normally.
2. `KLocalNonzero`: generalise the `LIXHsq*` local square over the base chart, using the chart at `z_j` =
   one-zero chart ∘ swap ∘ `κ_j` (sp-oddside-n's `kSect`, rank-free, `LIXKGenSect`), so that
   `Ψ_k ∘ chart_j = P ∘ sphereChartVec` and the section read in `chart_j` is `P̃ ∘` the one-zero expression.
   Coordinate with lix-oddside-n, whose rank-`n` charts are centred at `−e₀` and need the same bundle side.
3. Odd `p`: `LocalClassesAgree` over `K` (Half A/B), with lix-coeff's `RelHomotopyIdentity`,
   `exists_relCocycle_splitOf`, `RelativeLocalModelOf.isUnit_localEquivOf_of_ne_zero`, and lix-cupone's
   `KroneckerSphere`. Move the LIXHsq* `RelativeLineHomotopy` uses to `RelHomotopyIdentity`.
4. Owed cleanup: the `linter.unusedSimpArgs false` guards in LIXKMap, LIXKSection, LIXKPunctured,
   LIXKStepCWired (they compiled in rescue-lix's gates; the flagged args need a probe to identify).

## NEEDS

* lead: ruling on who builds the bundle-side local computation at a general zero (rank 2 here, rank `n`
  for lix-oddside-n) so it is built once.

## TRAPS

* (lix-oddside, 09-11) `LocalSplit` lives over `[Field K]` (`LIXKCount`), so a generic-ring split theorem
  must state the equation form `x = ∑ …` and convert at `ZMod 2`.
