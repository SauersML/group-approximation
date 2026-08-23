---
rg: 2
id: monomial-finite-phase-ce-kernel-face-gap
kind: claim
title: Find a finite-phase projective-kernel face of the monomial trace containing no CE trace
artifacts:
  - research/artifacts/monomial-toric-factor-clause-audit-2026-08-23.md
distinct_from:
  monomial-finite-phase-projective-kernel-face-separator: that targets finite-dimensional vector-state separation plus realization as a finite game; this asks for the stronger CE-tracial face exclusion and needs no game testability afterward.
  non-ce-trace-does-not-promote-to-subgroup-character-gap: that refutes the implication for arbitrary non-CE traces; this asks whether the finite-phase monomial linking structure supplies the additional normal subgroup whose whole face is non-CE.
  bcs-projective-kernel-phase-compilation: that tries to wordize nonlinear BCS predicates through a finite gadget; this permits any finite-phase normal subgroup of the monomial question group and phrases the endpoint directly in trace space.
---

**OPEN.**  Let `A_mon` be an `s`-monomial game algebra with a trace and no
nonzero homomorphism into `R^omega`.  Choose an extreme trace `tau`, and let

```text
pi_tau:G_A x G_B -> U(L^2(A_mon,tau))                  (MCE1)
```

be its standard two-player group representation.  Find a normal subgroup
`K` of the finite universal question group and a conjugation-invariant
finite-phase character

```text
chi:K -> mu_q,          pi_tau(k)=chi(k)I,             (MCE2)
```

such that

```text
F_(K,chi) intersect T_CE(G_A x G_B)=empty.             (MCE3)
```

Then `ce-projective-kernel-face-gap-gives-nonhyperlinear-quotient` produces
the finitely presented nonhyperlinear group directly.  No finite game or
full-corner monomial algebra is needed after `(MCE3)`.

Necessary checks are sharp.  `K` cannot be trivial; `chi` cannot extend to a
character of the ambient question group; and the associated graph quotient
cannot be hyperlinear, because its regular defining-character corner would
be a CE state in `(MCE3)`.  Thus this is a smaller **interface** than toric
game groupification, but proving it is already a direct group obstruction.

The monomial gap alone does not prove `(MCE3)`.  It excludes CE traces which
factor through the full monomial losing ideal.  The projective-kernel face
can contain unrelated CE traces unless scalar word equations recover that
ideal on every tracial state.  Establishing exactly that recovery is the
remaining source-specific problem.

