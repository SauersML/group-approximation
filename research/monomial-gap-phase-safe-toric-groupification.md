---
rg: 2
id: monomial-gap-phase-safe-toric-groupification
kind: claim
title: Groupify a finite-phase monomial game gap with phase-safe normal closure
distinct_from:
  phase-safe-toric-gap-implies-nonhyperlinear: that proves the endpoint after a phase-safe toric game is already given; this must convert the monomial quantum-reflection game into that input.
  central-word-state-face-compiler: that starts directly from the non-RU BCS trace face; this starts from a finite-phase monomial linking algebra already carrying the qc/qa gap.
  finite-phase-monomial-game-algebra-dictionary: that is an exact game-algebra theorem and does not assert that its scalar phase survives group normal closure.
---

**OPEN.**  Given a finite `s` and an `s`-monomial matrix pair `(A,B)` whose
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

## Attempts

- Replacing the phase-resolved projections by independent cyclic group
  letters preserves the local answer table but need not preserve the linking
  algebra or its `R^omega` obstruction.
- Normal closure is stronger than survival of the phase in one perfect
  representation.  Directly centralizing monomial clause words can normally
  generate the scalar phase, exactly as in the existing extraspecial and
  spherical-root firewalls.
- The active target is a full-corner groupification whose perfect tracial
  model is inherited from the monomial algebra; a local phase calculation is
  insufficient.
