---
rg: 2
id: endpoint-five-moving-cut-drift-proof
kind: route
title: Compute the zero fivefold meet and expose the endpoint chart coboundary
target: endpoint-five-moving-cuts-have-zero-meet-and-gauge-drift
requires:
  - endpoint-order-five-actor-has-half-gram
  - full-packet-cyclic-aggregates-retain-positive-endpoint-gram
  - endpoint-odd-actor-retains-native-factor-gauge
---

In the ordered root basis `(e_1,e_2,e_3,e_4)=(C_3,s,t,s')`, the exact
conjugation formulas `(OFG4)` are

```text
M:e_1|->e_1+e_3, e_2|->e_3, e_3|->e_1+e_2, e_4|->e_4,
W:e_1|->e_1,     e_2|->e_4, e_3|->e_3,     e_4|->e_2.
```

Therefore `C=WM` has

```text
C:e_1|->e_1+e_3, e_2|->e_3, e_3|->e_1+e_4, e_4|->e_2,
```

and iteration gives `(EMC4)`.  A joint character lying under all five
conjugates of the raw cut `1_(e_1=-1,e_2=+1)` must vanish on every vector
in `(EMC4)`.  The occurrences of `e_2,e_3,e_4` make those three character
coordinates zero, while the occurrence of `e_1+e_4` makes the first one
zero as well.  This contradicts the negative `e_1` sign.  Since `p_2` is
below the raw cut, `(EMC2)` follows.

For the chart assertion, let

```text
Phi_j:E_j H -> L_j tensor K
```

be any five packet charts and suppose

```text
Phi_(j+1) (E_(j+1) C E_j) Phi_j^(-1)=m_j tensor D_j.
```

Replacing `Phi_j` by `(1 tensor S_j)Phi_j` gives `(EMC6)` by direct
multiplication.  Multiplying the five displayed transition equations and
using `E_5=E_0`, `C^5=1` shows that only the cyclic product is
chart-invariant.  Starting with the tautological transported charts makes
all five reservoir factors one.  Applying `(EMC7)` gives `(EMC8)` and
keeps `Phi_0` unchanged.  Hence all operators compressed entirely inside
`E_0`, including the endpoint Whitehead compression and its polar, are
unchanged.

Finally `(EMC10)` fixes the product `M=J_2(B_3A_2)` and therefore every
expression in `W,M,C,p_2` while changing the two factors separately.  This
is exactly the paired factor symmetry proved in the required claim.  It
shows that even a hypothetical choice of charts canonical from the actor
data could not recover the native-factor occurrence: the actor data are
identical on the two sides of `(EMC10)`.
