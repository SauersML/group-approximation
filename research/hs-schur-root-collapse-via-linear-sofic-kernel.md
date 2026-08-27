---
rg: 2
id: hs-schur-root-collapse-via-linear-sofic-kernel
kind: route
title: Apply stable finiteness to the coefficient quotient decoded from the root kernel
target: hs-schur-toeplitz-root-defect-collapse
requires:
  - hs-steinberg-root-kernel-is-linear-sofic
---

Let `Phi` be the putative homomorphism in `(HST1)` and let `K_Phi` be
`(SRK2)`.  If `R_f/K_Phi=0`, the marked root is already trivial.  Otherwise
`hs-steinberg-root-kernel-is-linear-sofic` embeds this quotient in a
rank-metric matrix ultraproduct.

Rank-metric matrix ultraproducts are stably finite.  This follows
coordinatewise from the matrix rank identity for the two defects of a
one-sided inverse and remains true after every fixed matrix amplification;
it is also Proposition 2.8 of Arzhantseva--Paunescu, *Linear sofic groups
and algebras* (arXiv:1212.6780).

The images of the Toeplitz coefficients in the quotient satisfy `yx=1`.
Stable finiteness therefore gives `xy=1`, so

```text
P_f=1-xy=0 mod K_Phi.
```

Thus `P_f in K_Phi` and `Phi(x_12(P_f))=1`, which is the qualitative
ultraproduct conclusion of `hs-schur-toeplitz-root-defect-collapse`.
