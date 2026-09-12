# lx-endpoint — D1 assembly and Palomar readiness (LIX strongest swarm, 2026-09-12)

Clone lix-a. Owns `Manuscript/NinetyNineProblems/ProblemLIXStrong*`, `CharClass/LIXLemmaTwoGen*`, the Palomar LIX-strong surface,
Palomar scripts/workflows, `formalization.yaml`.

## LANDED AND COMPILED

| sha | module | evidence |
|---|---|---|
| e1cd56947 | `ProblemLIXStrongAssemblyTwo` (named Props `LemmaTwoPowersTwoLocalData n`, `LemmaTwoPowersTwoWuData n`; `lemmaTwoHoldsForSections_powersSections_two`, `lemmaTwoHoldsAtPowers_two_pow`) | probe 0912-101459-43218 BUILT, md5 610d4232… = origin |
| 890a5989f | `ProblemLIXStrongAssemblyOddP` (named Prop `LemmaTwoPowersModPData n p` over `ZMod p`; `stepCHalf_of_eq_zero_imp` and htop restricted to mapping tori of continuous corner unitaries, per lx-review (a); `lemmaTwoHoldsAtPowers_of_twoData_of_modPData`, `lemmaTwoHoldsAtPowers_of_modPData`) | probe 0912-102827-68823 BUILT, md5 614f7dba… = origin |
| 650084c64 | D4: `Palomar/LIXStrongChallenge.lean` + `LIXStrongSolution.lean` gain `(∀ (m : ℕ) (x : CStarMatrix (Fin m) (Fin m) A), star x * x = 1 → x * star x = 1)` after separability in all three theorems; solution discharges it via `exists_isSimpleRing_separable_stablyFinite_hasK1InjPowerWitness_of`; shared block byte-identical (also to `LIXChallenge.lean`) | palverify 0912-105804-22079 (SLURM acn91, base 63eeb5e54): build rc=0 (4 LIX Palomar libs), strong axioms rc=0 ([propext, Classical.choice, Quot.sound] ×3), strong statement drivers rc=0, self-test rc=0; the plain submission check has one infra finding (job clone is not a git checkout).  Bytes f54b36b5… / c972e386… = origin |
| 2648d3624 | challenge docstring: "one nontrivial element" (lx-review (c)) | docstring only |
| (reports) | `notes/lix-strong-swarm/lx-endpoint.md` | 16637bbc4, 988016fbc |

All five verified on the restored tip 3ba3746c8 (after becc912bd wiped main at 11:10 and 3f71a3a50 restored it at 11:20).

## THE PRIME 2 IS CLOSED: the stronger theorem at every rank 2^m, unconditional

| sha | module | evidence |
|---|---|---|
| 58f87fe90 | `ProblemLIXStrongAssemblyTwoLocal`: `lemmaTwoPowersTwoLocalData_holds n := CharClass.KGen.kZeroLocalData_powers n` (lx-local2b, 142fedcac); `lemmaTwoHoldsAtPowers_of_wuData_of_modPData`; `lemmaTwoHoldsAtPowers_two_pow_of_wuData` | probe 0912-115408-95665 (lix-a, base 1302f8022, PROBE GREEN, 9494 jobs): `Built … ProblemLIXStrongAssemblyTwoLocal (30s)` |
| 58f87fe90 | `ProblemLIXStrongAssemblyTwoWu`: `lemmaTwoPowersTwoWuData_holds n [NeZero n]` (baseY, Sphere 1 / 2n+1, KnLix.prY/prS1/prSodd, hasSphereCohomology_sphere, sphereTopClass, `Gen.nonempty_wuStepDData_lixN`, lx-slice2 e0d8365e0); **`lemmaTwoHoldsAtPowers_two_pow_holds m`**, **`exists_isSimpleRing_separable_hasK1InjPowerWitness_two_pow m`** | same probe: `Built … ProblemLIXStrongAssemblyTwoWu (20s)`; axiom lines read by name, each `[propext, Classical.choice, Quot.sound]`; sorryAx 0 |

Producers frozen by their owners: `KGen.kZeroLocalData_powers` (lx-local2b), `Gen.wuStepDData_lixN` / `nonempty_wuStepDData_lixN` (lx-slice2).

## THE ODD PRIMES OVER TWO INPUTS (e2c63d7dc, landed unverified, probe running)

`ProblemLIXStrongFinal.lean`:
* `lixTopGen p n j` (abbrev) = `ChernSplittingOf.cpGenOf (ZMod p) (1 + LH.tautCardOf (Gen.VIdx n dd ⊕ Gen.VIdx n dd)) _`.
* named Prop **`LixStepCDataOf n p`**: ∀ k, ¬ p ∣ k → ∀ j G hGc hGu hGe, ∃ u, `KGen.KGenLocalNonzeroOf (ZMod p) n (k-1) … u` ∧
  `jE u = π^* (lixChernDegOf (ZMod p) n dd (lixTopGen p n j) W (lixRank n dd))`, i.e. the hdata of `stepCHalf_of_localNonzeroOf`.
  Producer: lx-sliceK's `KGen.exists_localNonzeroOf_hclassOf_cpGen (ZMod p) n (k-1) (lixDD n j) hGc hGu hGe` (planned
  `CharClass/LIXKGenOfStepCThomClosed.lean`; leaves: htaut (lx-sliceK), hchart (lx-stepcK-agree), hgamma
  `neg_hyperLHOf_gamma_eq_lixChernDegOf` and `kGenLocalNonzeroOf_of_top_closed`, both compiled 0912-122241-8475).
* `lemmaTwoPowersModPData_of n p ops hC` at the real objects: baseY, S¹, S^{2n+1}, KnLix projections, `sphereTopClassOf (ZMod p)`,
  `Gen.realTorusModP_lixStage ops` (compiled 0912-121048-60132), `Gen.expChar_evenPart_baseY`, LE/LV from
  `compactLerayHirschDualOf_cpGen`, hhomE `LerayHirschDataEvenOf.chern_eq_of_graded`, q := `KGen.negEZero n`, κ := 1,
  hwu `KGen.hasSplittingPN_lixBundleOf_self`, clause (ii) by rfl, clause (iii) `kZeroStepCDataOf_of_localNonzeroOf`.
* `lemmaTwoHoldsAtPowers_of_oddPrimeData n hn2 ops hC` (prime 2 discharged), endpoint
  `exists_isSimpleRing_separable_hasK1InjPowerWitness_of_oddPrimeData`, `eq_three_of_prime_dvd_six`,
  `lemmaTwoHoldsAtPowers_six_of ops3 hC3`.
* The reduced powers input is `evenReducedPowersOddP p hp hunit hmul htop hbad μ hμ hcp` (lx-pzero, binders frozen; UnitZero and
  TopTwo from lx-toppower, PtotMul and BadTwo from lx-cartan-b, ZeroCP needs a line bundle on T² with a nonzero Euler class, which
  nobody owns).

### RED at probe 0912-122422-14351 (lix-a, base e2c63d7dc): a duplicate declaration in two peer files

`ProblemLIXStrongFinal.lean:1:0: import GroupApproximation.CharClass.ChernSplittingOfCompact failed, environment already contains
'GroupApproximation.CharClass.nontrivial_evenPartOf' from GroupApproximation.CharClass.SliceValueVOf`.  The two statements differ:
lx-splitK `ChernSplittingOfCompact:110 (K) [CommRing K] [Nontrivial K] (Y)` with 2 uses in its own file, and lx-sliceK
`SliceValueVOf:55 (X) [Nontrivial (TotalHOf K X)]` with 4 uses in `SliceNaturalOf`/`SliceSplitVOf`.  Final is the first module
importing both.  Lead's ruling: lx-splitK renames its copy to `nontrivial_evenPartOf_of_nonempty` (call sites in its own file);
lx-sliceK keeps its copy.  Re-probe Final after lx-splitK's sha and a clean dupcheck.  None of Final's own code was elaborated.

dupcheck.py e2c63d7dc ProblemLIXStrongFinal (MSI, `$P/lixs-dupcheck/final-e2c63d7dc.out`): closure 5922 → 6055 (133 newly
reachable), 4 predicted collisions: `nontrivial_evenPartOf` (real) and `by`, `is`, `of` (prose false positives).

## OPEN (odd primes; `LemmaTwoPowersModPData n p`)

* T: `Gen.realTorusModP_lixStage ops n j` (lx-torusP), needs a producer of `OddPTotal.EvenReducedPowers p` (lx-pzero; none on main).
* bundle data: lx-bundleP's `Gen.nonempty_realBundleModP_lixChernDegOf_stages` (not on main at 8cbc0c5fa), binders hgen, LE/LV
  (lx-lhK-b), hhomE, hwu (lx-splitK).
* ExpChar: `Gen.expChar_evenPart_baseY p dd` (GREEN).  γfun/topClass via `KGen.lixChernDegOf` (htop rfl).
* Step C over K: `KGen.kZeroStepCDataOf_of_localNonzeroOf K n k dd … u hlocal hclass` (on main); needs `KGenLocalNonzeroOf` at the
  Thom class and `hclass` over K (lx-stepcK-local/agree).
* `ProblemLIXStrongFinal.lean` not authored: odd-prime producer spellings still moving.

## PALOMAR, when D1 lands

Add the three unsuffixed wrappers to `LIXStrongSolution.lean`; rename the axioms/solution drivers' names (drop `_of`, move the
boundary to the end); move `comparator-lix-strong.json` to `PALOMAR_CONFIGS`; formalization.yaml rows from the axioms run; Cairn text;
dispatch the real Comparator.  `$LX/palverify.sh` (+ `remote/palverify.template.sh`) runs the surface job on lix-a via SLURM.

## TRAPS

* zsh: `"$B:path"` loses the colon suffix; `path` is zsh's PATH array — a loop variable named `path` kills every command.
* The palverify summary grep also shows the self-test's PLANTED findings; read the `=== STEP submission` block.
* lxland clobber guard on a path last changed by another lane: pass `NM_BASE=<origin sha the copy was read at>`.
* lxland exits 6 silently under a filtering grep when `$LX/HALT` exists; read unfiltered output.
* ENOSPC on the Mac (11:05–11:20) made git plumbing fail mid-landing; a commit built from an empty index wiped main (becc912bd).
