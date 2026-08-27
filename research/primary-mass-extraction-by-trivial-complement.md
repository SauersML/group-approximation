---
rg: 2
id: primary-mass-extraction-by-trivial-complement
kind: route
title: Replace the primary summand by trivial blocks and apply the coprime projective modulus
target: fixed-projective-gap-forces-primary-congruence-mass
requires:
  - sl3-odd-correctable-sector-has-uniform-projective-modulus
---

Let `P` and `Q=1-P` support `sigma_coprime` and `sigma_primary`.  Replace the
second summand by the trivial representation:

```text
tilde_sigma(lambda)
 = P sigma(lambda) P + Q.                                (PME1)
```

This is an exact representation of `Lambda`.  Because only finitely many
irreducibles occur and every irreducible on `P` has minimal conductor
coprime to `p`, `tilde_sigma` factors through one congruence level coprime to
`p` (take the least common multiple of those minimal conductors).

For every lattice generator `c`, the two exact representations differ only
on a subspace of normalized dimension `m`; hence

```text
||sigma(c)-tilde_sigma(c)||_2 <= 2 sqrt(m).               (PME2)
```

Therefore `rho|_Lambda` is within `xi+2 sqrt(m)` of the coprime exact
representation `tilde_sigma`.  Substitution into the established odd-sector
modulus gives `(PMG2)`.

If the far energy is at least `epsilon` while the argument of `eta_odd` were
at most `s_epsilon`, `(PMG2)` would contradict
`eta_odd(s_epsilon)<epsilon`.  Rearranging gives `(PMG3)`, and taking a
liminf gives `(PMG4)`.  No invariance of the two conductor summands under the
approximate denominator generator is assumed or needed.
