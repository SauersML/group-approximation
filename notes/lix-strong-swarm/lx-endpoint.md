# lx-endpoint — D1 assembly and Palomar readiness (LIX strongest swarm, 2026-09-12)

Clone lix-a. Owns `Manuscript/NinetyNineProblems/ProblemLIXStrong*`, `CharClass/LIXLemmaTwoGen*`, the Palomar LIX-strong surface,
Palomar scripts/workflows, `formalization.yaml`.

## Design (09-12)

* `ProblemLIXStrongAssemblyTwo.lean`: named Props `LemmaTwoPowersTwoLocalData n` (binder `hloc` of
  `CharClass.Gen.lemmaTwoFor_powers_two_lixChernOf`, producer lx-local2b) and `LemmaTwoPowersTwoWuData n` (∃ spaces, maps,
  sphere data, with `Nonempty (Gen.WuStepDData …)` at every stage and corner unitary; producers lx-kunneth + lx-slice2);
  `eq_two_of_prime_dvd_two_pow`, `lemmaTwoHoldsForSections_powersSections_two`, `lemmaTwoHoldsAtPowers_two_pow`.
* `ProblemLIXStrongAssemblyOddP.lean`: `stepCHalf_of_eq_zero_imp`, `natCast_sub_one_add_one_ne_zero`, named Prop
  `LemmaTwoPowersModPData n p [Fact p.Prime]` over `K = ZMod p` (∃ spaces/maps/sphere pieces, `T : ∀ j, RealTorusModP`,
  `∀ j, ExpChar (evenPart (ZMod p) (Y j)) p`, `γfun`, `topClass : … → Hmod (ZMod p) (lixN) (2·KGen.lixRank)`, with
  (i) `Nonempty RealBundleModP` for every mapping torus, (ii) `htop : γfun j W (∑dd + (n+1)) = TotalHOf.of … (topClass j W)`,
  (iii) `KGen.KZeroStepCDataOf (ZMod p) n (k-1) (lixDD n j) … (topClass j (mapping torus))` for `p ∤ k`);
  `lemmaTwoHoldsForSections_powersSections_of_modPData`, `lemmaTwoHoldsAtPowers_of_twoData_of_modPData`,
  `lemmaTwoHoldsAtPowers_of_modPData` (odd rank).
* Later `ProblemLIXStrongFinal.lean`: `lemmaTwoHoldsAtPowers n hn` once the producers of the three named Props land.

## GREEN

(none yet)

## AUTHORED, UNVERIFIED

* `ProblemLIXStrongAssemblyTwo.lean`, `ProblemLIXStrongAssemblyOddP.lean`: landed unverified e1cd56947; probe 0912-101459-43218 running on lix-a.

## NEEDS

* lx-local2b: `LemmaTwoPowersTwoLocalData n` (i.e. `KGen.KZeroLocalData` at every odd exponent / stage / G).
* lx-kunneth + lx-slice2: `LemmaTwoPowersTwoWuData n` for even `n`.
* lx-torusP, lx-bundleP, lx-stepcK-local/agree, lx-lhK-b: `LemmaTwoPowersModPData n p` at odd `p`.

## TRAPS

* zsh: `"$B:path"` loses the colon suffix; write `"${B}:path"`.
