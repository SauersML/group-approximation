---
rg: 2
id: bounded-area-high-chromatic-conjugacy-collapse
kind: claim
title: A bounded-area high-chromatic conjugacy graph collapses its marked word in matrix microstates
distinct_from:
  coherent-carmichael-family-forces-thompson-three-cycle-collapse: that is the complete-graph Carmichael specialization; this is the reusable criterion for arbitrary finite graphs of unbounded chromatic number and arbitrary bounded-area relator certificates.
  word-recursion-cannot-amplify-sublinear-summands: that rules out manufacturing macroscopic mass from a reducing small corner; this begins with one conjugacy orbit and uses compactness plus high chromaticity to force a close related pair in the full ambient matrix dimension.
  thompson-v-r5-cap-implies-one-word-collapse: that constructs a full approximate alternating-group multiplication table and invokes finite-group stability; this needs only order-three vertex relators and order-two edge products, with no table or exactification.
---

Let

```text
G=<X | R>,                 delta_R(U)=max_(r in R)||r(U)-I||_2
```

be a finite presentation, and fix a word `w` in the free group on `X`.
Suppose there are finite graphs `Lambda_n`, words

```text
u_v=h_v w h_v^(-1),       v in V(Lambda_n),
```

and an integer `L>=1`, independent of `n`, such that

```text
chi(Lambda_n) -> infinity,                                  (BHC1)
Area_R(u_v^3)<=L,                                            (BHC2)
Area_R((u_v u_z)^2)<=L       whenever vz is an edge.         (BHC3)
```

Here `Area_R(q)<=L` means that the free word `q` is a product of at most
`L` conjugates of elements of `R union R^(-1)`.  Then every unitary matrix
tuple `U` satisfies

```text
||w(U)-I||_2 <= 2L delta_R(U).                               (BHC4)
```

Consequently `w` is killed by every homomorphism from `G` to a tracial
matrix ultraproduct.  If `w!=1` in `G`, then `G` is not hyperlinear.

The conjugating words `h_v` may have arbitrary length.  Their length never
enters `(BHC4)`: normalized Hilbert--Schmidt norm is unitarily invariant, and
only the number of relator cells in `(BHC2)--(BHC3)` is charged.

There is also a quantitative converse useful for screening sofic and amenable
actions.  Let `P_d(eta)` be the size of any finite `eta`-net of `U(d)`.  For a
single graph with `chi(Lambda)>P_d(eta)`, let `L_Lambda` be the maximum of all
cube and edge areas.  Then every matrix tuple with positive presentation
defect satisfies

```text
L_Lambda >= (||w(U)-I||_2-4 eta)/(2 delta_R(U)).          (BHC5)
```

Thus a regular-character microstate gives an explicit area-growth lower
bound once the graph is chosen post hoc beyond its unitary packing number.
There is no dimension-free numerical rate because hyperlinearity supplies no
rate relating matrix dimension and presentation defect.

For Thompson `V`, the exact conjugacy graph of common-pivot three-cycles
contains cliques of every finite size.  Thus the remaining R5 problem is
precisely to choose word representatives for those vertices whose cube and
edge loops have uniformly bounded R1--R5 area.  Abstract conjugacy or a
depth-dependent van Kampen derivation is insufficient.
