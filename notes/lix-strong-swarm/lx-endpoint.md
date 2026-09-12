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

## AUTHORED, NOT LANDED (HALT file in $LX; both on disk, copies in $LX/backup/d4/)

* `ProblemLIXStrongAssemblyTwoLocal.lean`: `lemmaTwoPowersTwoLocalData_holds n := CharClass.KGen.kZeroLocalData_powers n`;
  `lemmaTwoHoldsAtPowers_of_wuData_of_modPData`; `lemmaTwoHoldsAtPowers_two_pow_of_wuData`.  Waits on lx-local2b's
  `LIXKGenLocalNonzero` compiling (one `rw [map_zero]` red, fix landing).
* `ProblemLIXStrongAssemblyTwoWu.lean`: `lemmaTwoPowersTwoWuData_holds n [NeZero n]` (baseY, Sphere 1 / 2n+1, KnLix.prY/prS1/prSodd,
  hasSphereCohomology_sphere, sphereTopClass, `Gen.nonempty_wuStepDData_lixN`); **`lemmaTwoHoldsAtPowers_two_pow_holds m`** and
  **`exists_isSimpleRing_separable_hasK1InjPowerWitness_two_pow m`** — the stronger theorem at ranks 2^m, unconditional once the two
  producers compile.  Waits on lx-slice2's `LIXStepDGenWuData` (red on a missing `open scoped Matrix`).

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
