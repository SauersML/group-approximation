---
rg: 2
id: permutation-gauge-law-proof
kind: route
title: Expand the corrected defect and move the source correction through the second factor
target: relation-defects-obey-permutation-gauge-law
requires: []
---

Using `(PGL2)` and then inserting `sigma_h sigma_h^(-1)` around `c_g`,

```text
tilde_delta
 = (sigma_k c_k)^(-1)(sigma_g c_g)(sigma_h c_h)
 = c_k^(-1) sigma_k^(-1) sigma_g c_g sigma_h c_h
 = c_k^(-1) sigma_k^(-1) sigma_g sigma_h
   (sigma_h^(-1)c_g sigma_h)c_h
 = c_k^(-1) delta
   (sigma_h^(-1)c_g sigma_h)c_h.
```

This is `(PGL3)`, and setting the displayed product equal to the identity is
equivalent to `(PGL4)`.