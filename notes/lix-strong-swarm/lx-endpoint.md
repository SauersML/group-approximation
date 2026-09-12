# lx-endpoint — D1 assembly and Palomar readiness (LIX strongest swarm, 2026-09-12)

Clone lix-a. Owns `Manuscript/NinetyNineProblems/ProblemLIXStrong*`, `CharClass/LIXLemmaTwoGen*`, the Palomar LIX-strong surface,
Palomar scripts/workflows, `formalization.yaml`.

## Design (09-12)

* `ProblemLIXStrongAssemblyTwo.lean`: named Props `LemmaTwoPowersTwoLocalData n` (binder `hloc` of
  `CharClass.Gen.lemmaTwoFor_powers_two_lixChernOf`) and `LemmaTwoPowersTwoWuData n` (∃ spaces, maps, sphere data, with
  `Nonempty (Gen.WuStepDData …)` at every stage and corner unitary); `eq_two_of_prime_dvd_two_pow`,
  `lemmaTwoHoldsForSections_powersSections_two`, `lemmaTwoHoldsAtPowers_two_pow`.
* `ProblemLIXStrongAssemblyOddP.lean`: `stepCHalf_of_eq_zero_imp` (restricted to mapping tori of continuous corner unitaries),
  `natCast_sub_one_add_one_ne_zero`, named Prop `LemmaTwoPowersModPData n p [Fact p.Prime]` over `K = ZMod p`
  (∃ spaces/maps/sphere pieces, `T : ∀ j, RealTorusModP`, `∀ j, ExpChar (evenPart (ZMod p) (Y j)) p`, `γfun`,
  `topClass : … → Hmod (ZMod p) (lixN) (2·KGen.lixRank)`, with (i) `Nonempty RealBundleModP` at every mapping torus,
  (ii) htop at mapping tori of continuous corner unitaries (rfl for `γfun W k := of (2k) (c_k W)`), (iii)
  `KGen.KZeroStepCDataOf (ZMod p) n (k-1) (lixDD n j) … (topClass j (mapping torus))` for `p ∤ k`);
  `lemmaTwoHoldsForSections_powersSections_of_modPData`, `lemmaTwoHoldsAtPowers_of_twoData_of_modPData`,
  `lemmaTwoHoldsAtPowers_of_modPData` (odd rank).
* Planned `ProblemLIXStrongFinal.lean`: `lemmaTwoHoldsAtPowers n hn := lemmaTwoHoldsAtPowers_of_twoData_of_modPData n hn …`.
* D4 (ratified with lx-stablyfinite): inline conjunct after separability in the three strong challenge theorems,
  `(∀ (m : ℕ) (x : CStarMatrix (Fin m) (Fin m) A), star x * x = 1 → x * star x = 1) ∧`; solution bridge
  `NinetyNineProblems.lixLimit_isStablyFiniteMatrices n` (`Manuscript/NinetyNineProblems/LIXStablyFinite.lean`).  Applied
  only once that module is green.

## GREEN

* probe 0912-101459-43218 (lix-a, acn112 slot 3, base 4b9f8144d, PROBE GREEN, 9458 jobs): `BUILT ProblemLIXStrongAssemblyTwo`,
  `BUILT ProblemLIXStrongAssemblyOddP`; origin bytes (6c003072f) = green-record md5. Landed e1cd56947.
* Palomar job 0912-102309-23751 (SLURM acn30, base 6c003072f, LIX libs only, `$LX/palverify.sh`): build rc=0
  (PalomarLIXChallenge, PalomarLIXSolution, PalomarLIXStrongChallenge, PalomarLIXStrongSolution); strong axioms driver
  rc=0 with closure `[propext, Classical.choice, Quot.sound]` for each of the three `_of` stand-ins; strong statement
  drivers rc=0; submission self-test rc=0.  The plain submission check has ONE finding, "could not read the git index, so
  submodules could not be checked": the job runs in a clone that is not a git checkout, so this is infra, not a surface defect.

## AUTHORED, UNVERIFIED

* `ProblemLIXStrongAssemblyOddP.lean` at 890a5989f (htop weakened to mapping tori, lx-review finding (a)); re-probe queued on lix-a.
* `Palomar/LIXStrongChallenge.lean` docstring: "one element of order two" → "one nontrivial element" (lx-review finding (c)).

## NEEDS / producer names announced

* p = 2 local: lx-local2b `CharClass.KGen.kZeroLocalData_powers n : LemmaTwoPowersTwoLocalData n` (body identical), in
  `CharClass/LIXKGenLocalNonzero.lean` (not compiled yet).
* p = 2 Wu: lx-slice2 `CharClass.Gen.wuStepDData_lixN n [NeZero n] j G hGc hGu` over lx-kunneth's `KnLix.prY/prS1/prSodd`,
  `sphereTopClass`, `hasSphereCohomology_sphere` (`CharClass/LIXStepDGenWuData.lean`, not compiled yet).
* odd p: lx-bundleP `Gen.realBundleModP_stages(_deg)` (`CharClass/LIXStepDGenBundlePLix.lean`, unverified),
  `Gen.expChar_evenPart_baseY` (GREEN 0912-102525-49371); γfun/topClass via lx-stepcK-local's planned degreewise
  `KGen.lixChernDegOf K n dd hgen W k` (htop rfl); lx-torusP `T`; lx-stepcK-local/agree `KZeroStepCDataOf`.
* D4: lx-stablyfinite `lixLimit_isStablyFiniteMatrices` (probe launched on lix-a).

## TRAPS

* zsh: `"$B:path"` loses the colon suffix; write `"${B}:path"`.
* The Palomar job's summary error grep also collects the self-test's PLANTED findings (`::error::` lines inside planted
  copies).  Read the `=== STEP submission` block of the log, not the summary grep.
* lxland clobber guard on a non-probed path (Palomar docstring): the guard needs `NM_BASE=<origin sha the copy was read at>`
  when the last origin commit on the path is not your own landing.
