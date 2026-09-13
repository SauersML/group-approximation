---
rg: 2
id: serre-class-admits-non-integral-atoms
kind: claim
title: The Serre class contains a measure with an atom at 1/2 and one with Galois-unequal atoms, so it is not the set of integer-matrix spectral limits
invalidates: [integral-limits-via-serre-converse]
distinct_from:
  serre-class-atoms-obey-degree-bound: that proves the one constraint the class forces on atoms; this shows by explicit measures that the class forces nothing more
  integer-moment-measure-with-negative-log-determinant: that is a Galois-unequal atomic measure outside the class; this puts Galois-unequal atoms inside the class by adding a compensating equilibrium part
  integer-root-limits-are-galois-balanced-serre-measures: that characterizes the integer-matrix limits inside the class; this exhibits members of the class outside them
artifacts:
  - research/artifacts/determinant-spectral-atoms-2026-09-12.md
  - research/artifacts/determinant-integer-root-limits-2026-09-12.md
---

**ESTABLISHED** by `serre-class-admits-non-integral-atoms-proof`.

Let `omega_R` be the arcsine (equilibrium) measure of `[-R, R]`. Both

```text
mu_1 = 1/2 delta_(1/2) + 1/2 omega_4,
mu_2 = 0.3 delta_(phi^2) + 0.1 delta_(phi^-2) + 0.6 omega_6,     phi = (1+sqrt 5)/2,
```

satisfy `integral_(Q != 0) log|Q| d mu >= 0` for every nonzero `Q in Z[x]`.
Neither is a weak limit of eigenvalue distributions of integer matrices with real
spectrum:
- `mu_1` has an atom at a non-integer;
- `mu_2` has unequal masses on the conjugates `phi^2`, `phi^-2`;
- such limits carry atoms only at totally real algebraic integers, balanced on
  conjugates (`integer-root-limits-are-galois-balanced-serre-measures`).

**Consequences.**
- `serre-class-measures-are-integral-spectral-limits` is false: the Serre class
  is strictly larger than the set of integer-matrix spectral limits, symmetric
  or not.
- Route `integral-limits-via-serre-converse` is dead.
- At the level of one spectral measure, the determinant conjecture forces
  neither integral eigenvalues nor equal conjugate multiplicities. The corrected
  converse adds exactly that balance.
