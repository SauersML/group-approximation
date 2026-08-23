---
rg: 2
id: triangle-kernel-corner-leakage-proof
kind: route
title: Compress a kernel-relator residual before applying multipath Gram coercivity
target: triangle-kernel-relators-charge-authenticated-corner-leakage
requires:
  - triangle-colimit-llp-reduces-to-relator-local-splitting
  - finite-multipath-average-coercivity-has-exact-julia-absorber
---

The triangle-colimit theorem identifies the complete non-tree relation family
as the finitely many words `n_a=1`.  Since `(1-q)q=0`,

```text
(1-q)Y_aq=(1-q)(Y_a-I)q.
```

Left and right compression are contractions in Hilbert--Schmidt norm, so

```text
||(1-q)Y_aq||_2<=||Y_a-I||_2.                          (TKL4)
```

The left side squared is
`tau(qY_a^*(1-q)Y_aq)`.  Divide by `beta=tau(q)` to obtain `(TKL1)`.

For `(TKL2)`, use `(1-p)Zq=0` and write

```text
(1-p)Yq=(1-p)(Y-Z)q.
```

The same compression estimate proves the claim.

Finally apply `(MPA3)` with `p=q`, `C=qY_aq`, and
`L=qY_a^*(1-q)Y_aq`.  Substitute `(TKL1)` into its leakage term to get
`(TKL3)`.  All constants are independent of the representation dimension;
only the authenticated carrier density `beta` enters.
