# lx-local2b — the local square at the k+1 zeros, and `KZeroLocalData` at p = 2, rank n

Lane of the LIX strongest swarm (lead: main session nonsofic-existence-39). Clone lix-b, shared with lx-local2a.
Owns `CharClass/LIXKGenLocalSquare*`, `LIXKGenLocalNonzero*`, the existing `LIXKGenLocal{Split,Eta,Linear,Pair,Res,Nbhd}`, `LIXKLocal*` and `LIXKStepCExponent*`.

## Split with lx-local2a (agreed 09-12)
lx-local2a writes `CharClass/LIXKGenLocalHomotopy.lean` (landed unverified at fb1085202). It holds the homotopy and every leg map, their mapsTo lemmas and ends. It has no cohomology, so that lx-stepcK-local can reuse it over a field. This lane writes everything cohomological at ZMod 2: the cut, far = GR', the two chains, the rfl identifications, and the nonvanishing. There is no `LIXKGenLocalLegs` file.

## Route (no excision at the base)
For each zero `z_i` take `B := lixKTrivBall n k dd i`, which contains no other zero.
1. Left leg: `relPullback GL = (lixKSRel ≫ restrictTo B C) ≫ relPullback lixKChartPt` (`relPullback_lixKGL_chain`).
2. Square: `relPullback GL = relPullback GR` (`relPullback_lixKGL_eq_lixKGR`), by cutting the homotopy over `lixKULine` and removing `lixKGMap` (`relPullback_lixKGHomeo_eq_id`).
3. Right leg: `relPullback GR = (lixKRes ≫ bundlePairIso.hom ≫ prodIso.hom ≫ excF.hom) ≫ relPullback shrink` (`relPullback_lixKGR_chain` + rfl lemmas).
4. If `restrictTo B C (σ^* u) = 0`, then the right leg kills `u`. The shrink is injective and the excision is an iso, so `lixKLocalPairIsoClosed (lixKRes u) = 0`, contradicting `lixKLocalPairIsoClosed_lixKRes_ne_zero`.

## GREEN
* lx-local2a's `LIXKGenLocalHomotopy`: PROBE GREEN 0912-102831-69207 (their record).
* Probe 0912-103648-14016 (lix-b, base 7e8a94ac9) FAILED on ONE error, `LIXKGenLocalSquare.lean:126:32 unsolved goals`
  (`relPullback_lixKGL_chain`: `rw [s1, s2]` left a goal whose two sides print identically). Every other declaration of the
  Square compiled: `relPullback_lixKFar_eq_lixKGR'` and `relPullback_lixKGL_eq_lixKGR`, both with axioms
  [propext, Classical.choice, Quot.sound], plus `relPullback_lixKGR_chain` and all five rfl identifications. Fix: add an explicit `rfl`.
  Nonzero was not reached.
* **Probe 0912-110847-76784 (clone lix-j, base eb8320e00): `BUILT` + `COMPILED` `CharClass/LIXKGenLocalSquare`**
  (record `lanes/lx-local2b.green.0912-110847-76784`). Nonzero had ONE error at 71:12, `rw [map_zero]` pattern not found:
  the zero introduced by `h0` is typed at a differently spelled relative group. Every downstream declaration elaborated
  and inherited only sorryAx: `kGenLocalNonzero_lixThomClassTerm`, `kZeroLocalData_holds`, `kZeroLocalData_powers`,
  `stepCHalf_two_powers_lixChernOf_holds`, `printedKZeroLocalData`. Fix: term-mode `congrArg`/`trans`/`map_zero _` chains.

* **PROBE GREEN 0912-114043-43603 (clone lix-j, base 9f8227f46): `BUILT GroupApproximation.CharClass.LIXKGenLocalNonzero`,
  `COMPILED` LIXKGenLocalSquare + LIXKGenLocalNonzero** (record `lanes/lx-local2b.green.0912-114043-43603`). The build
  passed every `#audit_axioms` and `#audit_closed_axioms KGen.printedKZeroLocalData`. **`KGen.KZeroLocalData n k dd hGc
  hGu hGe` is a theorem for every n, k, dd, G** (`kZeroLocalData_holds`), with no positivity hypothesis.

## INCIDENT 11:17 CDT: main wiped by a peer
* Commit becc912bd ("Import Evington--Pennig triviality ...", 11:10:52 -0500, trailer session_01PWzwKNBr2dwjX4pucBuXff)
  deleted 27,760 paths. Parent ce16f64eb holds 27,760 files; tip bff8f642a holds 23. Lead alerted by SendMessage.
* My landing of the Nonzero fix + report was REFUSED (imports not on origin/main); nothing of mine is lost.
  Backups: `$LX/backup/lx-local2b/LIXKGenLocalSquare.lean` (= compiled bytes, probe 0912-110847-76784) and
  `LIXKGenLocalNonzero.lean` (fixed, never compiled).
* RESOLVED 11:20: forward restore 3f71a3a50 (session_018da4ZMvDEshSvGp3YdQgZQ) re-added every path of ce16f64eb. Tip
  810105d57 holds 27,781 files and my Square bytes equal the compiled bytes. The Nonzero fix is landed, and probe 3 follows at ~11:38.

## SPLIT
* none. The lane's work is two files: the Square is compiled except one line, and the Nonzero proof is authored.

## AUTHORED, UNVERIFIED
* `CharClass/LIXKGenLocalSquare.lean`: `relPullback_lixKFar_eq_lixKGR'`, `relPullback_lixKGL_eq_lixKGR`, `relPullback_lixKGL_chain`, `relPullback_lixKGR_chain`, `lixKExcF_hom_eq`, `lixKRes_eq`, `lixKBundlePairIso_hom_eq`, `lixKProdIso_hom_eq`, `lixKLocalPairIsoClosed_hom_eq`.
* `CharClass/LIXKGenLocalNonzero.lean`: `lixKRestrict_lixThomClassTerm_ne_zero`, `kGenLocalNonzero_lixThomClassTerm`, **`kZeroLocalData_holds`**, `kZeroLocalData_powers` (= lx-endpoint's `LemmaTwoPowersTwoLocalData n` body), `stepCHalf_two_powers_lixChernOf_holds`, `PrintedKZeroLocalData` / `printedKZeroLocalData` (`#audit_closed_axioms`).

## NEEDS
* none (lx-local2a's Homotopy is on main).

## TRAPS
* `rw [s1, s2]` closes the goal by `rfl` at REDUCIBLE transparency only. A composite's middle object can be spelled as
  `TopCat.of ↥B` with `B : Set (↥sphereOne × baseM)` in one term and with `B : Set ↑(lixN n dd)` in the other, e.g. when
  it comes from `LIXKRelMV.restrictTo (X := lixN n dd)`. The goal state then prints two identical sides and still reports
  "unsolved goals". Finish with an explicit `rfl`.
