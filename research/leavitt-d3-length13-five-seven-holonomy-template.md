---
rg: 2
id: leavitt-d3-length13-five-seven-holonomy-template
kind: claim
title: The length-thirteen five-seven topology carries an aligned HNN holonomy
artifacts:
  - research/leavitt-d3-length13-five-seven-holonomy-template-proof.md
distinct_from:
  leavitt-d3-length11-five-five-holonomy-template: that uses two equal five-valent residuals and leaves a rigid common-carrier equation; this adds one cancelling signed pair to only the target residual.
---

At degree three and length thirteen, a `(1,5,7)` cyclic-cover topology can
have residual sign patterns

```text
(-,+,-,+,+),                 (-,+,-,+,-,+,+).
```

After the unary pivot `z=H^(-1)`, assign the five-valent corners

```text
(H^(-1), H X, H^(-1) A, H Y, H B)
```

and the seven-valent corners

```text
(H^(-1), H X, H^(-1) C, H Y, H^(-1), H, H D).
```

They reduce exactly to `X A Y B` and `X C Y D`.  Hence the quotient contains
the HNN holonomy

```text
Y^(-1)(A^(-1)C)Y = B D^(-1),
```

and unequal-order choices such as `A^(-1)C=ab`, `BD^(-1)=cd` force
`[c,d]=1`.
