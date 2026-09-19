---
rg: 2
id: bs14-cell-lattice-coset-proof
kind: route
title: Separate affine saturation from additive padding by the incidence-lattice coset
target: bs14-native-cell-padding-preserves-lattice-charge
requires:
  - bs14-two-exit-typed-transport-is-not-saturated
---

For `(NCP2)`, write `s=A_En` with `n` integral.  If `b+s` belonged to
`S_E`, then both `s` and `b+s` would belong to `L_E`; subtracting would put
`b` in `L_E`, a contradiction.

For `(NCP3)`, each allowed column has bit labels `(i,j,k)` with
`i+j+k=0 mod 2`, so `omega` annihilates every column of `A_E`.  On the
six-unit margin vector it equals `1+1+1=1 mod 2`.  Doubling annihilates the
charge and `(TET6)` already supplies the integral doubled table.  This
proves simultaneously that the saturation exponent is two and that the
same-support additive padding distance is infinite.

