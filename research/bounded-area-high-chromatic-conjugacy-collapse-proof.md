---
rg: 2
id: bounded-area-high-chromatic-conjugacy-collapse-proof
kind: route
title: Color conjugates by a finite unitary net and collide one Carmichael edge
target: bounded-area-high-chromatic-conjugacy-collapse
requires: []
---

Evaluate a product of `k` conjugates of defining relators at a unitary tuple.
Unitary invariance and telescoping give

```text
||q(U)-I||_2 <= k delta_R(U).                                (1)
```

Put `B=w(U)` and `X_v=u_v(U)`.  Every `X_v` is an exact unitary conjugate of
`B`, while `(1)` and `(BHC2)--(BHC3)` give

```text
||X_v^3-I||_2<=L delta_R(U),
||(X_vX_z)^2-I||_2<=L delta_R(U)       for vz in E(Lambda_n). (2)
```

Fix the matrix dimension `d` and `eta>0`.  Compactness of `U(d)` in normalized
Hilbert--Schmidt distance gives a finite `eta`-net with, say, `P_d(eta)`
points.  Color each vertex `v` by a nearest net point to `X_v`.  Choose `n`
with `chi(Lambda_n)>P_d(eta)`.  Some edge `vz` is monochromatic, so

```text
||X_v-X_z||_2<=2 eta.                                       (3)
```

Writing `A=X_v` and `C=X_z`, unitary telescoping gives

```text
||A^4-(AC)^2||_2<=2||A-C||_2.                               (4)
```

Since multiplication by `A^3` is unitary,

```text
||A-I||_2
 =||A^4-A^3||_2
 <=||A^4-(AC)^2||_2+||(AC)^2-I||_2+||I-A^3||_2
 <=4 eta+2L delta_R(U).                                    (5)
```

The left side equals `||B-I||_2`, because `A` and `B` are unitarily
conjugate.  The graphs need not be nested, and no estimate for
`P_d(eta)` is used.  Letting `eta` tend to zero proves `(BHC4)`.

For one graph, repeat the same calculation with `L_Lambda` in place of `L`
and do not let `eta` tend to zero.  Rearranging

```text
||w(U)-I||_2 <= 4 eta+2L_Lambda delta_R(U)
```

proves `(BHC5)` whenever `delta_R(U)>0`.  If the defect is zero and the
numerator is positive, the same argument says that such a graph cannot have
chromatic number above `P_d(eta)`.

If `U_k` represents a homomorphism to a tracial matrix ultraproduct, then
`delta_R(U_k)->0`, so `(BHC4)` kills `w`.  Hyperlinearity would supply such a
homomorphism with regular character; for `w!=1` that character has
`||w-I||_2^2=2`, a contradiction.
