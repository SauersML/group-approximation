---
rg: 2
id: no-linear-symplectic-splitting-of-truncated-weyl-levels
kind: claim
title: The truncated-polynomial Weyl tower has no module-linear symplectic one-level inclusion
distinct_from:
  truncated-polynomial-binary-weyl-expander-tower: that constructs an F_2-linear symplectic inclusion; this proves why that inclusion cannot also respect the full truncated-polynomial module action.
---

Let `R=F_2[u]`, `R_n=R/(u^n)`, and equip `V_n=R_n^2` with the
top-coefficient symplectic form `(TPW1)`. There is no injective `R`-linear
map

```text
j:V_n -> V_(n+1)
```

whose image is symplectically nondegenerate. In particular, there is no
`R`-linear symplectic inclusion compatible with all scalar-module operations,
so the one-qubit inclusion in
`truncated-polynomial-binary-weyl-expander-tower` cannot be equivariant for
the full elementary-linear action.

