---
rg: 2
id: capacity-gated-common-corner-bcs-two-cell-proof
kind: route
title: Pull every context covariance row back to the one common source projection
target: capacity-gated-common-corner-bcs-two-cell
requires: []
---

For one incidence write `D=AV-VZ`, with `V^*V=Q` and rounded
self-adjoint contractions `A,Z`.  Then

```text
V^*D-D^*V=ZQ-QZ,
```

so `||[Q,Z]||_2<=2||D||_2`.  Repeatedly substitute
`VZ_x=A_(c,x)V-D_(c,x)` through each fixed context word.  This gives

```text
||V R(Z)Q-R(A_c)V||_2
 <=C_R(sum_(x in c)||D_(c,x)||_2^2)^(1/2).
```

Because `V` is isometric on `Q`, the first term controls
`||Q R(Z)Q||_2`.  The complementary block `(1-Q)R(Z)Q` is bounded by
`[Q,R(Z)]`, and the preceding commutator estimate plus fixed-word
telescoping bounds that by the same covariance energy.  Add the target
residual `||R(A_c)V||_2`, square, and sum the finite residual menu.  This is
exactly `(CGC4)`, with a constant depending only on the fixed BCS.

The argument uses literal equality of the source projection `Q` for all
contexts.  Replacing it by context-private projections invalidates the first
commutator identity globally and is excluded by
`context-local-fanizza-exits-do-not-control-global-leakage`.

