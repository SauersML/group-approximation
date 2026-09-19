---
rg: 2
id: complement-unitary-projective-transfer-proof
kind: route
title: Transfer the ambient extension and return through polar Lipschitzness
target: projective-transfer-reduces-to-complement-unitary-extension
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
---

Fix `Z` and put `Uhat=U direct_sum Z`.  The exact arithmetic transfer theorem
gives

```text
E_H(Uhat,pi(h)) <= K sum_(c in S_C) E_H(Uhat,pi(c)),     (CUE4)
```

where `E(V,W)=1-|tr([V,W])|^2`.  Choose a scalar `z` minimizing the distance
from `[Uhat,pi(h)]` to the scalar unitaries.  Then

```text
||Uhat pi(h)-z pi(h)Uhat||_(2,H)^2
 =2-2|tr_H([Uhat,pi(h)])|
 <=2 E_H(Uhat,pi(h)).                                   (CUE5)
```

The `P`-corner of the left side is `UT_h-zT_hU`.  Changing from normalized
ambient norm to normalized corner norm costs `sqrt(D/m)`, so

```text
||UT_h-zT_hU||_(2,PH)^2
 <=(2D/m) E_H(Uhat,pi(h)).                              (CUE6)
```

Apply the standard polar Lipschitz estimate to

```text
A=UT_hU^*,                    B=zT_h.
```

Both have least singular value at least `sigma`; their polar factors are
`U rho_h U^*` and `z rho_h`.  Hence

```text
||U rho_h U^*-z rho_h||_(2,PH)
 <=(2/sigma)||UT_h-zT_hU||_(2,PH).                      (CUE7)
```

For a unitary commutator, projective energy is at most its squared distance
to any scalar.  Combining `(CUE4)--(CUE7)` yields

```text
E_PH(U,rho_h)
 <=(8K/sigma^2)(D/m) sum_c E_H(Uhat,pi(c)).              (CUE8)
```

Taking the infimum over `Z` proves `(CUE3)`.

Relative to `H=PH direct_sum (1-P)H`, the additive twisted commutator in
`(CUE5)` has four blocks.  Besides the corner phase condition it contains
terms of the form

```text
Z(1-P)pi(c)P-z_c(1-P)pi(c)PU,
UPpi(c)(1-P)-z_c Ppi(c)(1-P)Z,
```

and the projectively twisted complement-complement commutator (with the
minimizing scalar `z_c`).  Therefore `(CUE2)` is exactly a
joint synchronization condition on `U` and the raw compression boundary,
not a repackaging of polar relator defect.
