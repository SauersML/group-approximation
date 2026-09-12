---
rg: 2
id: uniform-bounded-area-clifford-collapse-proof
kind: route
title: Apply van Kampen telescoping and the all-pairs Clifford dimension floor
target: uniform-bounded-area-clifford-tables-force-mark-collapse
requires:
  - marked-clifford-table-exponential-dimension
---

For a unitary tuple `U`, evaluate

```text
f_N(g)=sigma_N(g)(U).
```

Each multiplication discrepancy in `(BAC2)` is a product of at most `A`
conjugates of defining relators and their inverses.  Unitary invariance and
telescoping therefore give

```text
||f_N(g)f_N(h)-f_N(gh)||_2<=A epsilon                  (1)
```

for every `N,g,h`.

If `||j(U)-I||_2>42Aepsilon`, apply
`marked-clifford-table-exponential-dimension` to `(1)`.  For every `N`,

```text
d>=(1-4A^2epsilon^2)2^N.                               (2)
```

No finite `d` satisfies `(2)` for all `N`, proving `(BAC3)`.  Since `j` is
nontrivial, canonical-trace hyperlinear microstates would have relator defect
tending to zero and `||j(U)-I||_2` tending to `sqrt(2)`, contradicting
`(BAC3)`.
