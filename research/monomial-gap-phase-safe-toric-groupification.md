---
rg: 2
id: monomial-gap-phase-safe-toric-groupification
kind: claim
title: Groupify a finite-phase monomial game gap with phase-safe normal closure
refuted_by: normal-phase-safe-toric-games-have-qa-one
distinct_from:
  phase-safe-toric-gap-implies-nonhyperlinear: that proves the endpoint after a phase-safe toric game is already given; this must convert the monomial quantum-reflection game into that input.
  central-word-state-face-compiler: that starts directly from the non-RU BCS trace face; this starts from a finite-phase monomial linking algebra already carrying the qc/qa gap.
  finite-phase-monomial-game-algebra-dictionary: that is an exact game-algebra theorem and does not assert that its scalar phase survives group normal closure.
  toric-clause-spectra-cannot-generate-monomial-factor: that rules out making the Fourier generators themselves into clause spectra; this remains open for a noncentral decoded full corner or a projective-kernel whole-face compiler.
artifacts:
  - research/artifacts/monomial-toric-factor-clause-audit-2026-08-23.md
---

**REFUTED.**  The proposed target asked: given a finite `s` and an
`s`-monomial matrix pair `(A,B)` whose
game algebra has a perfect commuting representation but no nonzero map to
`R^omega`, construct a finite torically determined game with

```text
omega_qc=1,              omega_qa<1,
N intersect B_phase={1},
```

or an equivalent perfect tracial model of the full toric universal algebra.
The construction must retain the Fourier phase projections of the
order-`s` quantum-reflection entries and certify that the scalar phase
survives the normal closure of all clauses.

This endpoint is impossible independently of the monomial source.
`normal-phase-safe-toric-games-have-qa-one` proves that every finite
two-player torically determined game with `N intersect B_phase={1}` has
`omega_qa=1`.  The normal quotient turns all clause components into central
one-player words; the phase label splits into a perfect product state, and
one-player RFD approximates it by finite-dimensional tensor strategies.

## Attempts

- Replacing the phase-resolved projections by independent cyclic group
  letters preserves the local answer table but need not preserve the linking
  algebra or its `R^omega` obstruction.
- Normal closure is stronger than survival of the phase in one perfect
  representation.  Directly centralizing monomial clause words can normally
  generate the scalar phase, exactly as in the existing extraspecial and
  spherical-root firewalls.
- `toric-clause-spectra-cannot-generate-monomial-factor`
  proves a stronger direct obstruction.  In every full tracial toric model,
  each player component of a clause is central in its player algebra, and it
  is scalar in an extreme/factorial monomial trace.  Hence the Fourier/sudoku
  projections cannot themselves be clause spectra generating the full
  monomial corner: that would make the corner commutative and create a map to
  `R^omega`.
- Decoding Fourier projections from other noncentral words does not evade
  the product-state theorem once the output is a normal phase-safe toric
  game.  The smaller finite-dimensional projective-kernel face route is
  independently refuted by
  `factor-split-projective-kernel-face-meets-fd-closure`: factorial
  left/right scalarity splits playerwise and produces a product state in the
  finite-dimensional closure.
- If one can strengthen the projective-kernel face exclusion from
  finite-dimensional vector states to **all CE traces**, finite-game
  testability is unnecessary: `ce-projective-kernel-face-gap-gives-nonhyperlinear-quotient`
  compactifies the face and produces a nonhyperlinear group directly.  This
  is wired as `nonhyperlinear-from-monomial-ce-kernel-face`.  The stronger
  hypothesis is not automatic—it already says that the associated central
  extension has no CE defining-character state.
