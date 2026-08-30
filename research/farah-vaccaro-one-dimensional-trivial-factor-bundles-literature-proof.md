---
rg: 2
id: farah-vaccaro-one-dimensional-trivial-factor-bundles-literature-proof
kind: route
title: Import Farah--Vaccaro's one-dimensional trace theorem
target: farah-vaccaro-one-dimensional-trivial-factor-bundles-have-only-uniform-traces
requires: []
---

Farah--Vaccaro, *Continuous selection of unitaries in II_1 factors*,
Proc. Amer. Math. Soc. 154 (2026), 1609--1622,
doi:10.1090/proc/17519, arXiv:2501.01272v3, Theorem 1.2, proves the
displayed trace representation for every II1 factor and every compact
Hausdorff base of covering dimension at most one.

Their Theorem 4.4 places, for each positive `a` and `epsilon>0`, a
projection `p` between `(a-epsilon)_+` and `a` in Cuntz order.
Theorem 1.1 supplies continuous Murray--von Neumann comparison of the
projection fields. The proof of Theorem 1.2 deduces strict comparison
relative to the point-mass traces, and Proposition 2.5 then identifies every
trace with some `rho_mu`.

The measure is unique because restriction to the central copy of `C(X)`
recovers it. Finally Cauchy--Schwarz gives

```text
|rho_mu(a)|^2 <= rho_mu(a*a) <= ||a||_(2,X)^2,
```

so every such trace is uniformly `2`-norm continuous. QED

This does not settle nontrivial W-star bundles. Farah--Vaccaro, Section 5,
explicitly isolates that extension: their Michael-selection multifunction
takes values in one fixed complete metric space, whereas a nontrivial bundle
has varying factor fibres. Higher-dimensional trivial bundles likewise
require uniform higher local connectivity, not merely fibrewise
contractibility.
