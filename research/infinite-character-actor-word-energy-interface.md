---
rg: 2
id: infinite-character-actor-word-energy-interface
kind: claim
title: Make finite word defects control an infinite character-orbit transport energy
---

OPEN.  Construct one finitely presented actor/module packet whose exact
elementary-abelian module has a nontrivial character set `Omega` satisfying
the infinite Schreier gap `(ISC1)`, and prove that normalized-HS relator
defect controls the summed PVM transport energy `(ISC2)` with a
dimension-independent modulus.

The packet must also exclude fixed or finite character classes which can
carry the D8 seed.  For a permutation module this usually requires removing
the constant character (for example by an augmentation relation); merely
using a transitive nonamenable actor is not sufficient.

Together with `one-seed-infinite-character-expansion-collapses-mark`, this
would be a one-scale capacity backend: no unbounded family, mixed Weyl table,
or post hoc choice of `n` remains.

## Attempts

- **Regular permutation module.**  The constant character is actor-fixed and
  can support a bounded exact model unless it is quotiented out.
- **Use group expansion without the energy interface.**  Word covariance on
  a few module generators does not automatically bound the sum over all
  spectral characters.  More sharply,
  `finite-covariance-energy-sees-only-character-restrictions` computes the
  exact block quadratic forms: a finite set `T` sees only restriction to
  `sT`, and every infinite character set has invisible same-label fibers.
  Thus finite-depth conjugacy recursion plus Schreier expansion cannot close
  the interface.  One fixed defect must encode infinite spectral resolution,
  or matrix-only rigidity must forbid motion inside those fibers.
- **Finite quotient modules.**  These return to the finite-orbit capacity
  theorem and require an unbounded family.
