---
rg: 2
id: bs14-relative-involution-proves-iwahori
kind: route
title: Repair the stable BS(1,4) core and then its single Iwahori involution
target: iwahori-local-global-defect-question
requires:
  - iwahori-square-root-presentation-is-bs14-plus-one-involution
  - bs14-unitary-representations-are-periodic-cycle-packets
  - bs14-relative-involution-extension-stability
---

Rewrite the corrected Iwahori presentation as

```text
<x,r,s | x^2, (xr)^2, (xs^2)^3, (xrs)^3,
          r s r^(-1) s^(-4)>.
```

The one-solenoid theorem first repairs the amenable `BS(1,4)` pair `(r,s)`
with a dimension-free modulus.  Word Lipschitzness transfers that change to
the four relations involving `x`.  Apply
`bs14-relative-involution-extension-stability` to repair `x` over the exact
core while preserving both cubic constraints.  The equivalent-presentation
claim then returns a compatible pair of modular vertex representations.
Composing the two moduli gives the function demanded by
`iwahori-local-global-defect-question`.
