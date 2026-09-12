---
rg: 2
id: infinite-chromatic-commutator-code-proof
kind: route
title: Color the first commutator entries by a finite unitary cover
target: infinite-chromatic-commutator-code-kills-mf-mark
requires:
  - bounded-relator-area-controls-opnorm-word-defect
---

Evaluate the presentation at a unitary tuple `U`, write

```text
epsilon=Def_R(U),
C_v=c_v(U), H_v=h_v(U), A_v=a_v(U), Z=z(U).
```

The bounded-area estimate gives

```text
||[C_v,H_v]-A_v Z A_v^(-1)||_op <= A_Delta epsilon,       (1)
||[C_w,H_v]-I||_op <= A_0 epsilon                         (2)
```

on every oriented edge `(v,w)`.

Fix `delta>0` and color `v` by a member of a finite operator-norm cover of
`U(d)` of diameter less than `delta` containing `C_v`.  Infinite chromatic
number gives an oriented edge `(v,w)` whose endpoints have the same color,
so `||C_v-C_w||_op<delta`.  For unitaries `A,B,H`,

```text
||[A,H]-[B,H]||_op <= 2||A-B||_op.                        (3)
```

Indeed, after cancelling the final `H^*`, insert `BHA^*` between `AHA^*`
and `BHB^*`.  Unitary conjugacy preserves distance from the identity, hence

```text
||Z-I||_op
 <= ||A_vZA_v^(-1)-[C_v,H_v]||_op
    +||[C_v,H_v]-[C_w,H_v]||_op
    +||[C_w,H_v]-I||_op
 <= (A_Delta+A_0)epsilon+2delta.                           (4)
```

For the infinite graph `delta` is arbitrary in the fixed matrix coordinate,
so `(4)` holds with the last term removed.  Along coordinate lifts of a
corona homomorphism, `epsilon` tends to zero because `R` is finite; therefore
`z` dies in the corona.  Normality of the MF residual gives the
normal-generation conclusion.

For a finite graph, the same coloring works when
`chi(G)>N_d(delta)` and gives `(CCC4)`.  Cover `U(d)`, viewed in the real
Euclidean space of dimension `2d^2` and Frobenius radius `sqrt(d)`, by
Frobenius balls of radius `delta/2`.  Frobenius distance dominates operator
distance, and the standard volumetric estimate gives `(CCC5)`.

