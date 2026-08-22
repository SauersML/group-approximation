---
rg: 2
id: projective-leak-polar-singular-collapse-proof
kind: route
title: Convert the leakage lower bound into a singular-value tail
target: fixed-projective-leak-forces-polar-singular-collapse
requires:
  - leakage-small-polar-compressions-obey-projective-transfer
---

Write

```text
ell_s=tr_PH(1-T_s^*T_s),            ell=sum_s ell_s.
```

The established transfer estimate and `(PSC1)` imply

```text
gamma <= K(sum_c E_c+ell) <= gamma/2+K ell,
```

so `ell>=gamma/(2K)`.  Hence some `s` satisfies

```text
ell_s>=a:=gamma/(2Kr)=2theta.                            (PSC4)
```

Let `X=1-T_s^*T_s`, so `0<=X<=1`, and let
`B=1_[theta,1](X)`, which is the projection in `(PSC2)`.  On `1-B` one has
`X<theta`, while on `B` one has `X<=1`.  Therefore

```text
2theta <= tr_PH(X)
          <= theta(1-tr_PH(B))+tr_PH(B)
          <= theta+tr_PH(B).
```

Thus `tr_PH(B)>=theta`, proving `(PSC3)`.  The constants are independent of
the ambient and retained dimensions.

