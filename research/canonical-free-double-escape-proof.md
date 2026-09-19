---
rg: 2
id: canonical-free-double-escape-proof
kind: route
title: Free-product two copies of the Slofstra--Vidick invisible mark
target: canonical-free-double-escapes-uniform-exact-projective-folding
requires:
  - exact-fd-invisibility-has-no-general-hs-robustification
---

Equation `(CFD1)` immediately gives `(CFD3)`: the commutator is the identity
for every auxiliary unitary `U`.  If `sigma:D -> U(d)` is an exact
representation, its restriction to either free factor is an exact finite-
dimensional representation of `K`.  Hence

```text
sigma(i_0(c))=sigma(i_1(c))=1,
```

which proves exact folding.

The free product of sofic groups is sofic, so `D=K*K` is sofic.  Free-product
normal form and `c!=1` show

```text
w=i_0(c)i_1(c)^(-1) !=1.                              (CFDP1)
```

Canonical sofic microstates are normalized-HS microstates with trace tending
to zero on every fixed nonidentity word.  Applying this to `(CFDP1)` proves
`(CFD4)`.

There is no compactness contradiction: an ultralimit of the canonical
microstates is an exact representation of `D` in a tracial matrix
ultraproduct, not an ultralimit of exact finite-dimensional representations.
The exact finite-dimensional representation variety is not HS-dense in this
canonical type.  That missing density/correction assertion is precisely
what a valid promotion theorem would have to add.
