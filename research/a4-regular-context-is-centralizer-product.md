---
rg: 2
id: a4-regular-context-is-centralizer-product
kind: claim
title: An exact regular mixed A4 context is exactly a product of the two cyclic centralizers
---

Let `rho` be a fixed unitary representation of `A4` which is a multiple of the
regular representation, and let `a,b in A4` be the standard generators with

```text
a^3=b^2=(ba)^3=1.
```

Write

```text
A=rho(a),
B=rho(b),
C_A=U(rho(<a>)'),
C_B=U(rho(<b>)').
```

For an arbitrary unitary `U` on the same Hilbert space, the following are
equivalent.

1. The mixed ordered pair `(A,U B U^*)` is unitarily equivalent, with the
   named A4 generators fixed, to the canonical pair `(A,B)`.
2. The relative unitary lies in the product of the two unitary centralizers:

   ```text
   U in C_A C_B.                                      (A4-CENT-PROD)
   ```

The statement is unchanged under arbitrary external amplification.  In
particular, after exact-regular normalization of an atlas A4 context, every
exact mixed context is one explicit centralizer-product constraint on the
relative chart frame.  No irreducible coordinates, qutrit carrier, or
multiplicity basis is needed for this equivalence.

This is a local compiler only: intersecting the packet constraints and
incorporating collision `19243` remains the global problem.
