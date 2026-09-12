---
rg: 2
id: stw83-kirchberg-core-circle-crowns-dimension-one-proof
kind: route
title: Exhaust the circle crowns by essential finite Kirchberg-by-circle extensions
target: stw83-kirchberg-core-circle-crowns-dimension-one
requires:
  - stw83-hereditary-finite-exhaustion-preserves-one
  - stw83-finite-kirchberg-core-circle-quotient-dimension-one
---

Let `H_n` consist of the vertices of `K` and of the first `n` blocks
`C_m union D_m`.  The direction assumptions make `H_n` hereditary: every edge
emitted in an included block remains in that block or enters `K`, while edges
emitted in `K` remain in `K`.  These finite sets increase to `E^0`.

For the induced finite graph `E_n`, set

```text
V_2 = K^0,
V_1 = union_(m<=n) D_m^0,
V_0 = union_(m<=n) C_m^0.
```

The graph on `V_0` is a disjoint union of simple cycles and `V_0` is already
saturated.  Indeed, order the finite acyclic connector vertices backwards from
`K`.  A connector adjacent to `K` has an edge outside `V_0`, so it is not added
by saturation; induction on distance to `K` gives the same conclusion for every
connector.  No core vertex is added because its emitted edges stay in `K`.
The graph on `V_1` is acyclic, and `K` is the required strongly connected
non-cycle core.  There are no paths from `V_2` back to `V_1` or `V_0`, nor from
`V_1` to `V_0`.  Finally, every vertex outside `K` reaches `K`.  Thus all five
hypotheses of `stw83-finite-kirchberg-core-circle-quotient-dimension-one` hold,
and `dim_nuc(C*(E_n))=1`.

Now `stw83-hereditary-finite-exhaustion-preserves-one` gives
`dim_nuc(C*(E))<=1`.  Since `E` contains a cycle, `C*(E)` is not AF; nuclear
dimension zero is equivalent to AF for separable C*-algebras.  Hence its nuclear
dimension is exactly one.
