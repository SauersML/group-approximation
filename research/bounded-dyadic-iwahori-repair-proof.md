---
rg: 2
id: bounded-dyadic-iwahori-repair-proof
kind: route
title: Apply fixed finite-diagram repair to the finitely many bounded dyadic quotient pairs
target: bounded-dyadic-conductor-iwahori-pairs-have-uniform-repair
requires:
  - fixed-finite-restriction-diagrams-have-linear-hs-repair
---

Fix `a,b<=A`.  Put `G_+=SL_2(Z/2^a)` and
`G_-=SL_2(Z/2^b)` (using the actual finite images if the displayed maps have
central kernel).  Reduction of the two vertex maps and the commensuration
give two homomorphisms from the abstract edge group `B_+` into these finite
groups:

```text
phi_+:B_+->G_+,                  phi_-=red_b o sigma:B_+->G_-.
```

Their joint kernel has finite index, so this is exactly a fixed finite
restriction diagram.  The defect on the standard Iwahori generators is
`(FDR1)`.  Apply
`fixed-finite-restriction-diagrams-have-linear-hs-repair` to obtain exact
representations of `G_+` and `G_-`, in the original dimension, whose pulled
edge actions agree literally and whose vertex matrices move by at most
`C_(a,b) def`.  Pulling them back to the two modular vertices gives an
exactly compatible pair.

There are only finitely many pairs `(a,b)` with `a,b<=A`; take

```text
K_A=max_(a,b<=A) C_(a,b).                              (BDP1)
```

This proves `(BDI2)`.  Notice why the argument does not silently solve the
full problem: both the finite edge quotient and its two restriction
matrices change with `(a,b)`.  Neither the fixed-group intertwiner gap nor
the integer Hoffman constant in the finite-diagram theorem is asserted
uniformly as `max(a,b)->infinity`.

