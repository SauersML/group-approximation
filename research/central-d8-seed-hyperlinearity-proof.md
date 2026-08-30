---
rg: 2
id: central-d8-seed-hyperlinearity-proof
kind: route
title: Read the Pauli seed as a finite-edge amalgam
target: central-d8-seed-preserves-hyperlinearity
requires:
  - amenable-edge-graph-corners-cannot-groupify-a-nonce-game
---

Put

```text
V_1=G x <J>,       V_2=D_8=<b,z,J>,       E=<b,J>.
```

Both maps `E->V_i` are injective because `b` is a nontrivial involution and
`J` is an independent central involution in `V_1`, while `<b,J>` is the
standard Klein four subgroup of `D_8`.  The presentation theorem for a free
product with amalgamation gives

```text
V_1 *_E V_2
 = <G,J,z | J^2=z^2=1, [J,G]=[J,z]=1, [b,z]=J>,
```

which is exactly `(CDS1)`.  This proves `(CDS2)`, including injectivity of
both vertices and nontriviality of `J`.

If `G` is hyperlinear, so is `G x C_2`; the other vertex `D_8` is finite and
the edge `E` is finite, hence amenable.  Apply
`amenable-edge-graph-corners-cannot-groupify-a-nonce-game` to the graph with
these two vertices and one edge.  Its fundamental group `(CDS2)` is
hyperlinear.  Conversely, subgroups of hyperlinear groups are hyperlinear,
and the embedded copy `G<=V_1<=P(G,b)` gives the reverse implication.
