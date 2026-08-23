---
rg: 2
id: leavitt-range-sum-fold-proof
kind: route
title: Compare the two range paths with one diagonal return in the same long root
target: leavitt-range-sum-fold-is-first-object-erasing-row
requires:
  - affine-active-corner-has-faithful-binary-leavitt-envelope
  - outer-root-leavitt-table
  - mixed-steinberg-loops-admit-morita-rectangular-model
---

Apply the four-root Steinberg identity

```text
[x_12(a),[x_23(1),x_34(b)]]=x_14(ab)
```

to the three coefficient pairs in `(LRF2)`.  The support identities
`As_i=s_i=s_iA` and `At_i=t_i=t_iA`, followed by the inverse and range-sum
relations `(LRF1)`, give `(LRF3)` and hence the null word `(LRF4)`.

For minimality, a source identity requires one path `t_is_i`; a target
identity cannot be represented by one path because each `s_it_i` is a proper
coordinate idempotent in the faithful Leavitt model.  Its first available
expression is the sum of the two range paths.  Therefore the three-path fold
is the smallest comparison which forgets the `E/F` object type.
