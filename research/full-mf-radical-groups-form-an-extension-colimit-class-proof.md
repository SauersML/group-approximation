---
rg: 2
id: full-mf-radical-groups-form-an-extension-colimit-class-proof
kind: route
title: Kill kernels first, quotients second, and reflect colimits
target: full-mf-radical-groups-form-an-extension-colimit-class
requires:
  - mf-equivalences-form-a-colimit-stable-localization
  - mf-radical-product-and-restricted-sum-formulas
---

Functoriality sends the full radical of a source onto a subgroup of the
radical of every quotient, proving quotient closure.

For an extension and a map `f:G->M` to an MF group, the restriction to `N`
is trivial.  Hence `f` factors through `Q`, where it is again trivial.  Thus
every such `f` is trivial and `G` has full radical.

If every object of a diagram has trivial MF reflection, preservation of
countable colimits gives

```text
R_MF(colim D)=colim_MF 1=1.
```

This proves colimit closure.  Free products and amalgams are colimits;
graph products are quotients of free products; directed unions are directed
colimits.  Products and restricted sums follow from the exact radical
formulas.  The last assertion is quotient closure plus the definition of
full radical.
