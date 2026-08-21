---
rg: 2
id: positive-density-modular-square-root-mixing-exclusion
kind: claim
title: Exclude a positive-density odd square-root mode between the two modular vertices
distinct_from:
  iwahori-unitary-commutant-transfer: that is the quantitative two-vertex commutant theorem; this is its exact projection normal form in tracial matrix ultraproducts.
  iwahori-local-global-defect-question: that asks to perturb the entire Iwahori pair to an exact compatible pair; this asks only for one block projection to commute with one square root.
---

OPEN.  Let `M=prod_omega M_(d_n)` be a tracial matrix ultraproduct.  Suppose
`X,Y in U(M)` satisfy the exact modular relations both for `(X^2,Y)` and for
`(X,Y^2)`.  Prove that every projection `P in M` satisfying

```text
[P,X^2]=[P,Y]=0                                      (MSX1)
```

also satisfies

```text
[P,X]=0.                                             (MSX2)
```

It is enough to prove `(MSX2)` under the additional nondegeneracy condition
that `P` and `1-P` are represented by matrix projections of trace at least
one fixed `c>0`: every failed transfer witness automatically has that form.

For `V=2P-1`, set

```text
W=XVX^*,       E=(V+W)/2,       A=(V-W)/2.           (MSX3)
```

Then `V,W` are involutions, conjugation by `X` swaps them, and

```text
E=E^*, A=A^*,  EA+AE=0,  E^2+A^2=1,
Ad_X(E)=E,     Ad_X(A)=-A,
||A||_2=||[P,X]||_2.                                 (MSX4)
```

Thus a counterexample is equivalently a macroscopic odd Clifford mode `A`
compatible with both modular structures.  The open task is to use the two
modular relations—not spectral squaring alone—to force this odd mode to
vanish in every tracial matrix ultraproduct.

## Attempts

- **Spectral squaring alone.**  Dead: a unitary can interchange the two
  square-root branches `lambda` and `-lambda` while its square preserves the
  cut.  This is exactly the nonzero `A` in `(MSX4)`.
- **Finite-type matching.**  Works on every fixed finite library of modular
  irreducibles, but does not control high-dimensional irreducible mass; that
  is the known unbounded Iwahori matching frontier.
- **Next attack.**  Insert the two braid/central modular relations for
  `(X^2,Y)` and `(X,Y^2)` into the odd/even decomposition `(MSX3)`.  The
  target is a dimension-free quadratic inequality bounding `||A||_2` by the
  two modular-relation defects.  No such inequality is currently proved.
