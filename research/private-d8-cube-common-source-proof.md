---
rg: 2
id: private-d8-cube-common-source-proof
kind: route
title: Compress every coordinate reflection to the bottom vertex of the finite role cube
target: private-d8-cube-has-one-common-source
requires: []
---

All projections belonging to different direct-product factors commute.
For a fixed context `c`, `j_c` commutes with every `p_(d,-)` for `d!=c`
and exchanges `p_(c,-)` with `p_(c,+)`.  Hence

```text
S_c^*S_c
 =Q j_c^*j_c Q
 =Q,

S_cS_c^*
 =j_cQj_c
 =p_(c,+) product_(d!=c)p_(d,-).                      (PDP1)
```

If `c!=d`, the range projection in `(PDP1)` for `c` contains
`p_(c,+)p_(d,-)`, whereas the range projection for `d` contains
`p_(c,-)p_(d,+)`.  Their product contains
`p_(c,+)p_(c,-)=0`, proving orthogonality.

The regular representation of a finite direct product is the tensor product
of the regular representations of its factors.  Normalized trace therefore
factorizes, giving `(PDC5)`.  Finally, the direct product and its complete
multiplication table are fixed and finite.  Flexible finite-group
Hilbert--Schmidt exactification moves its word matrices by a modulus depending
only on that table.  Evaluating the fixed group-algebra projections and the
fixed compressions `(PDC2)--(PDC3)` then perturbs `(PDP1)` by a
dimension-independent `o(1)` term.

Notice that the **uncompressed** `j_c` flips every edge parallel to the
`c`-th coordinate of the role cube.  It is not the Julia involution of only
the edge from `Q` to `S_cS_c^*`.  This is why the construction proves a
common source for row decoding but does not by itself establish the
canonical-trace swap-star compiler.

