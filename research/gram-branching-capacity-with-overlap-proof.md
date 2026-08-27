---
rg: 2
id: gram-branching-capacity-with-overlap-proof
kind: route
title: Compressed second moments bound overcrowding by leakage and Gram energy
target: gram-branching-capacity-with-overlap
requires: []
---

Put `R_a=T_aT_a^*` and `S=sum_a R_a`.  Each `R_a` is a projection and
traciality gives `tau(R_a)=tau(E_a)`, so

```text
tau(S)=s.
```

The off-target leakage is exactly

```text
l = sum_a tau((1-P)R_a)
  = tau((1-P)S),
```

hence, for the positive compression `B=PSP`,

```text
tau(B)=tau(PS)=s-l.                                  (1)
```

Cauchy--Schwarz in the finite tracial algebra, applied to `P` and `B`, yields

```text
tau(B)^2 <= tau(P) tau(B^2)=x tau(B^2).              (2)
```

Left and right multiplication by a projection are contractions in normalized
Hilbert--Schmidt norm, so

```text
tau(B^2)=||PSP||_2^2 <= ||S||_2^2=tau(S^2).          (3)
```

Expanding `S^2` gives

```text
tau(S^2)
 = sum_a tau(R_a) + sum_(a != b) tau(R_aR_b)
 = s + sum_(a != b) ||T_a^*T_b||_2^2
 = s+o.                                               (4)
```

Combining `(1)--(4)` proves

```text
(s-l)^2 <= x(s+o).
```

If `s+o=0`, then `s=0` and `(GBC2)` is immediate.  Otherwise divide and use
the exact scalar identity

```text
(s-l)^2
 = (s+o)(s-2l-o) + (l+o)^2.
```

Therefore

```text
x >= (s-l)^2/(s+o) >= s-2l-o,
```

which is `(GBC2)`.

For a branching target `j`, take the `T_a` to be all incoming branches.  Then
`s=sum_i a_ji x_i`; `(GBC2)` gives

```text
x_j >= sum_i a_ji x_i - (2l_j+o_j).
```

Thus the proof of `perron-frobenius-branching-carrier-collapse` applies
verbatim with effective error vector `2l+o`.  No matrix dimension, number of
branches, or minimal carrier rank enters the estimate.