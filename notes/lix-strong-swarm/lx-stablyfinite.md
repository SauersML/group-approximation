# lx-stablyfinite: stable finiteness of `LIX.Gen.LIXLimit n` (D4) and the Leray–Hirsch ladder over K (S3, S4)

Lane of the LIX STRONGEST swarm (lead nonsofic-existence-39, 2026-09-12).  Owns `Analysis/LIXLimitTrace*`,
`Analysis/LIXStageTrace*`, `Analysis/LIXStablyFinite*`, `Manuscript/NinetyNineProblems/LIXStablyFinite*`,
`CharClass/LerayHirschColSumOf.lean`, `CharClass/LerayHirschLadderClosedOf.lean`.  Clone lix-i.

## GREEN
- D4, probe 0912-102936-75396 (lix-a, base 16dabf296, PROBE GREEN, 8878 jobs): `BUILT` Analysis.LIXStageTrace,
  Analysis.LIXLimitTrace, Analysis.LIXLimitTraceFaithful, Analysis.LIXStablyFinite,
  Manuscript.NinetyNineProblems.LIXStablyFinite; `sorryAx` 0.  Probe 0912-104552-50230 (lix-i) rebuilt the manuscript
  module after `_pos` was added.  Landed 59a566d16, ab1856cca.
- S3+S4, probe 0912-120941-56371 (lix-i via SLURM acn49, base 5edf273be, PROBE GREEN, 9048 jobs): `BUILT`
  CharClass.LerayHirschColSumOf, CharClass.LerayHirschLadderClosedOf; `sorryAx` 0; no warnings.  The compiled
  evidence covers all seven lane files at the bytes on main.  S3/S4 landed at 60eceb761 (by lx-lhK-b from these disk
  bytes), attic copies at 572e33433.  The first S3+S4 probe, 0912-115920-18605, failed on two peer files (missing
  imports in CohomologyChartPeelUniqOf and ProjectiveSpaceRingBootstrapOf, both since fixed) and never reached S3/S4.
- Axioms, read by name, all `[propext, Classical.choice, Quot.sound]`: `LIX.Gen.nonempty_tracialState_lixLimit`,
  `lixLimitFaithfulTracialState`, `lixLimit_mul_star_eq_one_of_star_mul_eq_one`, `IsStablyFiniteMatrices`,
  `isStablyFiniteMatrices_iff`, `lixLimit_isStablyFiniteMatrices`, `lixLimit_isStablyFiniteCStarAlgebra`,
  `lixLimit_stablyFinite`, `lixLimit_two_isStablyFiniteMatrices`,
  `exists_isSimpleRing_separable_stablyFinite_hasK1InjPowerWitness_of`; `LH.hasFreeTuple_cpProdOf_of_ring`,
  `LH.ladderRingInputOf`, `LH.hasFreeTuple_cpProd_generalOf`, `LH.hasFreeTuple_cpProdOf`.

## What is proved
D4 (no hypothesis anywhere; independent of `LemmaTwoHoldsAtPowers`):
1. `STW59.Gen.stageTracialState n i w`: the normalized fibre trace is a tracial state on each stage algebra.
2. `LIX.CStarTower.nonempty_tracialState_limit`, for any tower whose levels carry tracial states: a compatible family by
   Cantor's intersection theorem in the compact product of trace spaces, passed to the colimit and extended to the
   completion.
3. `LIX.TraceFaithful.faithfulTracialStateOfIsSimpleCStar`: on a C⋆-simple algebra every tracial state is faithful
   (the null space is a closed proper two-sided ideal).
4. `LIX.Gen.lixLimit_mul_star_eq_one_of_star_mul_eq_one`: every isometry of every nonempty matrix amplification is a
   unitary.
5. `NinetyNineProblems.IsStablyFiniteMatrices A := ∀ (m : ℕ) (x : CStarMatrix (Fin m) (Fin m) A), star x * x = 1 →
   x * star x = 1` (Mathlib-only; lx-endpoint's inline conjunct), `lixLimit_isStablyFiniteMatrices n`,
   `lixLimit_stablyFinite n hn`, `exists_isSimpleRing_separable_stablyFinite_hasK1InjPowerWitness_of`.

S3/S4 (general-rank Leray–Hirsch over a field, unconditionally):
- `LH.colTowerOf`, `towerCoeff_colTowerOf`, `towerSumFun_colTowerOf`, `freeTuple_uniqueOf K U d hring h h0 n a hside hzero`
  (a column summing to zero is zero, by `KnCP.peelFreeAtOf`).
- `LH.hasFreeTuple_cpProdOf_of_ring K hring U d hfib hfib0`, `LH.ladderRingInputOf K : KnCP.CPRingOf K` (from
  `CPn.cupPowE_ne_zeroOf`), `LH.hasFreeTuple_cpProd_generalOf K U d hfib hfib0`, and
  `LH.hasFreeTuple_cpProdOf K U d _hd hfib hfib0 : HasFreeTuple (KnCP.cpFst U (d+1)) (pull (KnCP.cpSnd U (d+1)) 2 hfib) (d+2)`,
  consumed by lx-lhK-b's `LerayHirschCompactClosedOf`.

## AUTHORED, UNVERIFIED
None.

## NEEDS
None.

## SPLIT
Nothing left to split.

## TRAPS
- Local disk at 100% on 09-12 (913 MiB free): writes and landings failed silently for peers; check bytes after writing.
- `lxland.sh` refuses a module whose imports are absent from origin/main in every mode except NM_ATTIC, and a transient
  DNS failure (`Could not resolve host: github.com`) makes it exit at its first fetch: retry.
- A group probe can fail on peers' import bugs before reaching the lane's modules ("mentioned-not-built"): read which
  file is red before debugging your own.
