---
rg: 2
id: normalized-hs-null-loop-determinant-phase-proof
kind: route
title: Contract the HS-null subgroup and lift the rank-one winding loop
target: normalized-hs-null-loops-erase-determinant-phase
requires: []
---

For `U_n=diag(-1,1,...,1)`, direct calculation gives

```text
||U_n-I||_(2,d_n)^2=4/d_n,
det(U_n)=-1.
```

Thus determinant sign is not constant on a normalized-HS equivalence class.
For the loop `ell_n(t)` in the claim,

```text
sup_t ||ell_n(t)-I||_(2,d_n) <= 2/sqrt(d_n) -> 0,
det(ell_n(t))=exp(2 pi i t).
```

The unique lift of the determinant to a square root which begins at `+1` is
`exp(pi i t)`, so the lifted loop ends at `-1`. A cover which descended
through the HS quotient would be trivial on every loop contained in its
kernel; this one is not, proving the non-descent.

For path connectedness, choose the principal self-adjoint logarithm
`H_n` with spectrum in `[-pi,pi]`. The scalar inequality

```text
|theta| <= (pi/2)|exp(i theta)-1|,      |theta|<=pi,
```

gives `||H_n||_2 -> 0`. Functional calculus yields

```text
||exp(itH_n)-I||_2 <= t||H_n||_2 -> 0
```

for each `t`, while `||H_n||_op<=pi` makes the path continuous in the
uniform product of the normalized `2`-metrics. Hence the path stays in
`N_2`. A continuous image of this connected group in a discrete group is a
point, completing the proof.
