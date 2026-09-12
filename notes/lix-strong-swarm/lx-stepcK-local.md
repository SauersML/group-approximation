# lx-stepcK-local — local nonvanishing of Step C over a field K, rank n

Owns `CharClass/LIXKGen*Of*` / `LIXKGenOf*` except `LIXKGenOfStepC*`.  Clone lix-e.

## Deliverable
`KGenLocalNonzeroOf K n k hGc hGu hGe u` (LIXKGenLocalSplitOf:64) at the jE `u` of `KZeroStepCDataOf`; then
`exists_localSplit_ne_zero_kgenOf` gives `LocalSplit` + `∀ i, xloc i ≠ 0`.  Also the one K Chern class definition and
the `hgamma` leaf of lx-sliceK's `lixHclassOf_of_eq`.

## Route (no line trick) — all authored and landed
1. `KGen.restrictTo_relPullback_ne_zero_of_homotopy` (any ring): homotopy cut by `relPullback_eq_of_contractible_param`.
2. `KGen.lixKFarMap_relPullback_ne_zero`: far end = excision ∘ iso ∘ fibre map; only injectivity used.
3. `KGen.kGenLocalNonzeroOf_of_fibre` (B = `lixKTrivBall`) from `hfib : ∀ i, fibre_i^* u ≠ 0`.
4. `KGen.lixKFibre_relPullback_ne_zero_of_restrict`: singleton restriction ⇒ fibre class.
5. `KGen.kGenLocalNonzeroOf_of_top`: unit top Thom coordinate (`htop`) + L, per-zero L', hξ ⇒ step 3.
6. `KGen.kGenLocalNonzeroOf_of_top_closed`: L = `lixLHplusDualOf`, L' = `lixLHptDualOf`, hξ = `lixPtDual_hξ`; only
   `htop` remains = lx-sliceK's `thomJmTotalOf_lixThomClassTermOf_last`.
7. `KGen.kGenLocalNonzeroOf_neg` / `_smul` (LocalScale): nonzero multiples.
8. `KGen.neg_hyperLHOf_gamma_eq_lixChernDegOf` (ChernTop): `−γ_r(hyperplane) = lixChernDegOf … W r`, via
   `gamma_of_isoOf` and `component_chernEven_eq_neg_gammaOf` (`c_k = −γ_k` over K).

## GREEN (all bytes on main = compiled bytes)
* `LIXKGenOfLocalSquare` — probe 0912-111010-84153, BUILT + COMPILED.
* `LIXKGenOfFibre`, `LIXKGenOfFibreThom` — probe 0912-114035-42872, BUILT + COMPILED.
* `LIXKGenChernOf`, `LIXKGenOfThomLH`, `LIXKGenOfLocalScale`, `LIXKGenOfChernTop` — probe 0912-122241-8475, PROBE GREEN
  (9388 jobs), compiled records for all 7 files.

## AUTHORED, UNVERIFIED
* none.

## SPLIT
* none.  Unowned residuals reported by lx-sliceK to the lead: `htaut` (O(1) under the hyperplane inclusion with
  compatible generators `hgen = pull cpIncl hgen₊`) and `hchart` for `tautEulerDualK K hgen₊ W.plusOne`.

## NEEDS
* none (the K Thom class is lx-sliceK's, htaut/hchart unowned).

## TRAPS
* `rw [...]` then `simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]` before `exact` of a nested
  application: simp arguments reported unused (hard error); `exact` alone works.
* `TopCat.isoOfHomeo (e : A ≃ₜ B)` inline with no expected type (e.g. `(TopCat.isoOfHomeo e).symm.hom` inside a
  `ConcreteCategory.hom (…) q ∈ S` statement): "failed to synthesize instance" + application type mismatch.  Name the
  iso in a def with its declared `TopCat.of A ≅ TopCat.of B` type.
* `(x : TotalHOf K (lixN n dd))` for `x : ↥(Gen.evenPart K (TopCat.of X))`: Type mismatch, coercion search does not
  unfold the def `lixN`; use `x.1`.
* Over K, `LerayHirschGraded.gamma k = −c_k` (1 ≤ k ≤ r): the monic relation negates the coordinates.
* `tautCardOf`, `projMapOf` live in namespace `GroupApproximation.CharClass.LH`.
* A landing refused with "imports X, which is not on origin/main" for a long-landed X: check for a peer commit that
  deleted the tree (becc912bd, 09-12 11:20) before debugging the file.  `Could not resolve host: github.com` is
  transient DNS; retry after `git ls-remote` succeeds.
