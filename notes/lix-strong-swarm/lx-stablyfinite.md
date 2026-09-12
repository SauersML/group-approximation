# lx-stablyfinite: stable finiteness of `LIX.Gen.LIXLimit n` (D4)

Lane of the LIX STRONGEST swarm (lead nonsofic-existence-39, 2026-09-12).  Owns `Analysis/LIXLimitTrace*`,
`Analysis/LIXStageTrace*`, `Analysis/LIXStablyFinite*`, `Manuscript/NinetyNineProblems/LIXStablyFinite*`.

## GREEN
- Probe 0912-102936-75396 (lix-a, base 16dabf296, PROBE GREEN, 8878 jobs): `BUILT` lines for Analysis.LIXStageTrace,
  Analysis.LIXLimitTrace, Analysis.LIXLimitTraceFaithful, Analysis.LIXStablyFinite,
  Manuscript.NinetyNineProblems.LIXStablyFinite.  No errors, `sorryAx` count 0.
- Probe 0912-104552-50230 (base b3e39f5d9, PROBE GREEN): Manuscript.NinetyNineProblems.LIXStablyFinite `BUILT` again
  after the `_pos` variant was added; the compiled evidence covers all five files at their landed bytes.
- Axioms, read by name from the 102936 log: `[propext, Classical.choice, Quot.sound]` for
  `LIX.Gen.nonempty_tracialState_lixLimit`, `LIX.Gen.lixLimitFaithfulTracialState`,
  `LIX.Gen.lixLimit_mul_star_eq_one_of_star_mul_eq_one`, `NinetyNineProblems.IsStablyFiniteMatrices`,
  `isStablyFiniteMatrices_iff`, `lixLimit_isStablyFiniteMatrices`, `lixLimit_isStablyFiniteCStarAlgebra`,
  `lixLimit_stablyFinite`, `lixLimit_two_isStablyFiniteMatrices`,
  `exists_isSimpleRing_separable_stablyFinite_hasK1InjPowerWitness_of`.
- Landed: 59a566d16 (all five modules), ab1856cca (`lixLimit_isStablyFiniteMatrices_pos`).  Not wired into the root.

## What is proved
1. `STW59.Gen.stageTracialState n i w` (LIXStageTrace): `a ↦ r_i⁻¹ tr (a(w))` is a tracial state on each stage.
2. `LIX.CStarTower.nonempty_tracialState_limit` (LIXLimitTrace), for ANY tower whose levels carry tracial states.
   A compatible family comes from Cantor's intersection theorem in the compact `∏ T(A i)` (sets `compatibleBelow j`).
   It passes to the colimit (`colimTracialState`) and extends to the completion (`limTracialState`,
   `Completion.extension`; the laws follow by density).
3. `LIX.TraceFaithful.faithfulTracialStateOfIsSimpleCStar` (LIXLimitTraceFaithful): on a C⋆-simple algebra
   `traceKernel τ = {‖x‖₂ = 0}` is a closed proper two-sided ideal, so every tracial state is faithful.
4. `LIX.Gen.lixLimit_mul_star_eq_one_of_star_mul_eq_one n ι hι hv` (LIXStablyFinite): every isometry of every
   nonempty matrix amplification is a unitary, at every rank `n ≠ 0`.
5. `NinetyNineProblems.IsStablyFiniteMatrices A := ∀ (m : ℕ) (x : CStarMatrix (Fin m) (Fin m) A), star x * x = 1 →
   x * star x = 1` (Mathlib-only, the inline conjunct lx-endpoint adopts), `lixLimit_isStablyFiniteMatrices n`,
   `lixLimit_isStablyFiniteMatrices_pos n`, `lixLimit_stablyFinite n (hn : 2 ≤ n)`, `isStablyFiniteMatrices_iff`, and
   `exists_isSimpleRing_separable_stablyFinite_hasK1InjPowerWitness_of n hn (h : ClimbedPowersOutside n)`.

Stable finiteness is independent of `LemmaTwoHoldsAtPowers`: no hypothesis anywhere.

## AUTHORED, UNVERIFIED
None.

## NEEDS
None.  lx-endpoint changes the challenge, solution and drivers (inline conjunct, shape without `0 < m`).

## SPLIT
Nothing left to split.

## TRAPS
None hit: first probe green.  The design choices that avoided traps: stage traces use `inv_nonneg`/`mul_nonneg` in
`ComplexOrder`, as in `FaithfulTracialMatrix`, and the challenge rendering quantifies over an fvar size `m`
(never `Fin (k+1)`).
