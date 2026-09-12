---
rg: 2
id: compression-preimage-whitehead-preserves-gauge
kind: claim
title: A Leavitt-compression preimage of the moving Whitehead preserves its reservoir gauge
invalidates:
  - leavitt-preimage-whitehead-moving-bridge
artifacts:
  - research/compression-preimage-whitehead-gauge-proof.md
distinct_from:
  leavitt-compression-preserves-root-position-support: that applies compression to the signed Hecke cut and obtains the wrong support; this pulls the moving Whitehead itself back through compression and proves that its correct full Gram retains the old gauge.
  label-only-dressing-cannot-ungauge-a-whitehead-bridge: that surrounds one Whitehead by already ungauged normalizers; this tests the first genuinely nonnormal full-Leavitt opposite-root preimage occurrence.
  finite-extraspecial-mixed-words-cannot-ungauge-singer-transport: that fences finite normalizer extensions; this exits the finite extraspecial atom algebra through the Hilbert-hotel compression word.
---

**ESTABLISHED SCOPED NONNORMAL FENCE.**  Write

```text
W_ab(r,u)=x_ab(r)x_ba(u)x_ab(r),
alpha(r)=s_0 r t_0.
```

For the first literal moving Whitehead, the coefficient identities are

```text
alpha(s_0)=s_0s_0t_0=x_1,
alpha(t_0)=s_0t_0t_0=y_1,
alpha(W_87(s_0,t_0))=J_1.                              (CPW1)
```

Likewise `alpha(x_1)=x_2`, `alpha(y_1)=y_2`, so, after using positions
`(9,8)`,

```text
alpha(W_98(x_1,y_1))=J_2.                              (CPW2)
```

Let `T_i` be a coordinate copy of the explicit 20-by-20 compression word.
The Whitehead cell therefore gives exact ordinary elementary-group words

```text
T_1 W_87(s_0,t_0) T_1^(-1)=J_1,
T_2 W_98(x_1,y_1) T_2^(-1)=J_2.                       (CPW3)
```

These are the smallest natural genuinely nonnormal opposite-root candidates:
their preimage coefficients leave the finite extraspecial atom algebra, and
their images have exactly the required full Grams from `Q` to
`t_iQt_i^(-1)`.

They do **not** supply an ungauged bridge.  Put `Q'=J_iQJ_i^(-1)`,
`P=T_i^(-1)QT_i`, and `P'=T_i^(-1)Q'T_i`.  Then `(CPW3)` merely identifies
the gauge of `J_i:Q->Q'` after changing both charts: if the two restrictions
of `T_i` carry reservoir gauges `A,B`, then

```text
D_(J_i)=B D_(W_i) A^(-1).                              (CPW4)
```

There is no identity-outer occurrence forcing the right side to be `1`.
In particular, with `A=B=1`, any nontrivial multiplicity involution `D`
may be attached simultaneously to the two label Whiteheads, and all of
`(CPW1)--(CPW3)`, both involution laws, and all source/range Gram identities
remain exact.  Repeating this finite block gives a matrix-corona model of
this bounded occurrence table in which `||D-1||_2` stays positive.

Thus pulling back through the first full-Leavitt nonnormal occurrence only
pushes the same selector gauge one prefix level deeper.  It cannot establish
`(ESB2)` without an additional relation authenticating the preimage
Whitehead as identity on multiplicity.  No Property `(T)`, Kazhdan input,
trace profile, literature theorem, or Steinberg lift is used.

## Attempts

- **Use the two copies of `T_i` as cancelling gauge occurrences.**  They
  occur on different source/range cuts, so their factors give `(CPW4)`;
  cancellation would already assume the missing cross-cut gauge lock.
- **Iterate the coefficient preimage.**  This produces a finite chain of
  conjugate gauges.  A nontrivial involution placed at the deepest word and
  propagated upward satisfies every finite chain exactly.

DERIVATION
compression-preimage-whitehead-gauge-proof
