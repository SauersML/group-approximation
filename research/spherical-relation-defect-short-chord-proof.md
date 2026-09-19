---
rg: 2
id: spherical-relation-defect-short-chord-proof
kind: route
title: Compare both selected outputs through the common unitary product image
target: spherical-relation-defect-pairs-small-chord
requires: []
---

At a root satisfying the hypotheses, insert the three intermediate vectors
`U_g x_(sigma_h(i))`, `U_g U_h x_i`, and `U_k x_i`.  The triangle inequality
gives

```text
||x_(sigma_g sigma_h(i))-x_(sigma_k(i))||
 <= ||x_(sigma_g sigma_h(i))-U_g x_(sigma_h(i))||
  + ||U_g x_(sigma_h(i))-U_g U_h x_i||
  + ||U_g U_h x_i-U_k x_i||
  + ||U_k x_i-x_(sigma_k(i))||.
```

The first and last terms are at most `rho` by the `g`- and `k`-shadowing
bounds.  Unitarity of `U_g` turns the second term into
`||x_(sigma_h(i))-U_h x_i|| <= rho`.  The third term is at most `zeta` by
hypothesis.  Summing proves `(SRC3)`.