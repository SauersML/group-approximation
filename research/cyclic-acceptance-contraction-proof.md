---
rg: 2
id: cyclic-acceptance-contraction-proof
kind: route
title: Telescope the losses in the cyclic acceptance product
target: finite-game-gap-makes-the-cyclic-acceptance-compressor-strict
requires: []
---

Set `xi_0=xi`, `xi_j=Q_j xi_(j-1)`, and
`d_j=L_j xi_(j-1)`.  Orthogonality gives the exact telescoping identity

```text
||xi||^2-||Txi||^2=sum_j ||d_j||^2.                    (1)
```

Moreover,

```text
||L_j xi|| <= ||xi-xi_(j-1)||+||d_j||
            <= sum_(i<=j)||d_i||.
```

Cauchy--Schwarz therefore yields

```text
sum_j alpha_j ||L_j xi||^2
 <= alpha_max sum_j j sum_(i<=j)||d_i||^2
 <= alpha_max m(m+1)/2 sum_i||d_i||^2.                (2)
```

Combining the assumed lower bound with `(1)--(2)` proves the stated norm
estimate.  The reverse triangle inequality gives

```text
||(T-I)xi|| >= [1-sqrt(1-lambda/C)]||xi||,
C=alpha_max m(m+1)/2.
```

For a BCS Gram operator, predicate rejection is `G -> F_cG` and consistency
rejection is

```text
G -> (G-A_(c,x)GB_x)/2.
```

Both are orthogonal projections on `L^2(M_d)`, and the finite-game gap
supplies the assumed Rayleigh lower bound with `lambda=1-theta`.  Each
complement is a finite left-right operator, so their fixed product expands
as `sum_s beta_s U_s G V_s`, with finitely many rational coefficients and
words independent of `d`.  This proves both the contraction and finite
Hecke-expansion assertions.
