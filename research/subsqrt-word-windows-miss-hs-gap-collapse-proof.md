---
rg: 2
id: subsqrt-word-windows-miss-hs-gap-collapse-proof
kind: route
title: Telescope the rank-one surgery uniformly over growing word balls
target: subsqrt-word-windows-miss-hs-gap-collapse
requires:
  - irrep-window-does-not-force-hs-gap
  - finite-window-hs-tests-ignore-low-rank-generator-surgery
---

Use the same `SL_3(Z)` sequence as in
`irrep-window-does-not-force-hs-gap`.  Its proof gives a genuine irreducible
representation `rho_n` and an irreducible perturbed tuple `V_n` with

```text
max_s ||V_(s,n)-rho_n(s)||_2 <= C d_n^(-1/2)+d_n^(-2)
```

for a constant `C` depending only on the fixed generating set and the
rank-two surgery.  Property `(T)` gives a uniform adjoint gap for the exact
irreducible `rho_n`, while the normalized rank-one witness constructed there
makes the gap of `V_n` tend to zero.

The telescoping estimate of
`finite-window-hs-tests-ignore-low-rank-generator-surgery` is uniform over
words of a given length.  Hence every word `w` with `|w|<=L_n` satisfies

```text
||w(V_n)-rho_n(w)||_2
 <= L_n (C d_n^(-1/2)+d_n^(-2)).
```

If `L_n=o(sqrt(d_n))`, the right side tends to zero independently of `w`.
Taking the supremum over the whole word ball proves the stated uniform
indistinguishability while the two adjoint gaps stay separated.
