---
rg: 2
id: fixed-summable-residual-dominated-convergence-proof
kind: route
title: Apply dominated convergence to every fixed residual weighting
target: fixed-summable-kazhdan-residual-square-functions-vanish
requires: []
---

Fix `epsilon>0`.  Choose `J` such that

```text
4 sum_(j>J) a_j<epsilon/2.                              (KSP1)
```

The finite sum over `j<=J` tends to zero by `(KSV1)`, so for all sufficiently
large `n` it is less than `epsilon/2`.  The tail is bounded by `(KSP1)` because
`e_(j,n)^2<=4`.  This proves `(KSV2)`.

If `(KSV3)` held along a relative microstate sequence with
`||E_(B_n)(phi_n(h))||_2->0`, its left side would tend to one while its right
side tends to zero.  This proves the stated conditional exclusion.

For the exact-model firewall, use the canonical Fourier expansion in `L(G)`.
The trace-preserving expectation onto `L(Gamma)` kills `lambda(g)` exactly
when `g` lies outside `Gamma`, which proves `(KSV5)`, while the left regular
representation has zero multiplication residuals.  Since
`[Gamma:t Gamma t^(-1)]=infinity`, the quasi-regular representation has no
invariant vector.  Property `(T)` of `Gamma` therefore gives it a positive
spectral gap.  Thus the desired return loss and the Schreier gap coexist in an
exact zero-defect tracial representation, proving that Kazhdan expansion alone
cannot yield `(KSV3)`.
