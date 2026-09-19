---
rg: 2
id: stw99-lxxvi-unital-z-subalgebra-killing-proof
kind: route
title: Factor scalar extension through the K-stable unitary group of Z
target: stw99-lxxvi-unital-z-subalgebra-kills-unstable-scalar-classes
requires:
  - stw99-lxxvi-z-stabilization-kills-unstable-unitary-kernel
---

The scalar inclusion into `D` factors as

```text
C -> Z -> D.
```

Apply `stw99-lxxvi-z-stabilization-kills-unstable-unitary-kernel` with the
coefficient algebra `C`.  It says that the image of `alpha` in
`pi_k(U(M_n(Z)))` is zero.  Functoriality then makes its further image in
`pi_k(U(M_n(D)))` zero.
