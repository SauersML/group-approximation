---
rg: 2
id: torus-fourier-compressed-reynolds-proof
kind: route
title: Square the cubic rows and Fourier transform the signed Hecke compression
target: torus-fourier-gram-is-compressed-two-cubic-reynolds
requires: []
---

For an order-three unitary `L_A`, the cubic sum
`R_A=I+L_A+L_A^2` satisfies `R_A^*=R_A` and `R_A^2=3R_A`.
Conjugating by the displacement `L_(S^-2)` gives

```text
(R_A L_(S^-2))^*(R_A L_(S^-2))
 =9 P_(<S^2AS^-2>),
```

and the second row similarly gives `9P_(<SBS^-1>)`.  Restricting the domain
to `ran(QP_theta)` compresses, rather than merely restricts, this sum.  This
proves `(TFG3)`; positivity proves its kernel and frame formulas.

On a free right-torus orbit, substitute the Fourier vectors `(TFG8)` into a
matrix coefficient of `QL_gQ`.  Commutation of left and right translations
reduces the double sum to the difference `r=s t^(-1)`, giving `(TFG10)`.
Finite Fourier Parseval gives `(TFG12)`.  A delta correlation has constant
Fourier magnitude, proving the stated orthogonality firewall.

