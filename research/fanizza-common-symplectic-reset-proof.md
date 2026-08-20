---
rg: 2
id: fanizza-common-symplectic-reset-proof
kind: route
title: Verify the common symplectic reset hyperplanes over F2
target: fanizza-radical-charts-admit-common-symplectic-reset-subgroups
requires:
  - every-predicate-has-s3-equivariant-raw-radical-drop
  - three-radical-twist-crossed-products-have-uniform-scale
---

For each fixed Fanizza predicate and each nonzero chart direction `ell_i`,
form the odd alternating matrix `B_i(x)` in `(CHR1)`.  Exact Gaussian
elimination verifies that it has corank one for every Boolean assignment.
Solve the finite linear system

```text
phi_i(r_i(x))=1  for all x.
```

The printed witnesses solve all three systems.  Their kernels complement the
radical in every sector.  If a vector in `ker(phi_i)` is orthogonal to that
hyperplane, it is orthogonal to the radical as well and hence to the whole
odd space; it lies in both the radical and `ker(phi_i)`, so it is zero.
Therefore every restricted form is nondegenerate.  The artifact also checks
those restricted ranks directly.  Clifford representation theory then gives
the unique full-matrix type and the stated restriction multiplicity.
