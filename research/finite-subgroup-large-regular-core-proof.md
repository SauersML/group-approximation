---
rg: 2
id: finite-subgroup-large-regular-core-proof
kind: route
title: Extract the minimum Plancherel multiplicity across all irreducibles
target: finite-subgroup-near-regular-has-large-regular-core
requires:
  - gowers-hatami-finite-group-hs-stability
  - near-regular-finite-character-fixes-plancherel-types
---

Flexible finite-group stability gives exact `sigma_n` in
`d'_n=d_n+o(d_n)` dimensions.  Write its irreducible multiplicities as
`m_(pi,n)` and put `d_pi=dim(pi)`.  Near-regular character convergence gives

```text
m_(pi,n)/d'_n -> d_pi/|H|                              (FRC2)
```

for every `pi in Irr(H)`.  Define

```text
k_n=min_pi floor(m_(pi,n)/d_pi).                        (FRC3)
```

Since `Irr(H)` is finite, `k_n/d'_n -> 1/|H|`.  The regular representation
contains `pi` with multiplicity `d_pi`, so `(FRC3)` extracts an actual
`lambda_H^(sum k_n)` subrepresentation.  Its complement has dimension
`d'_n-k_n|H|=o(d'_n)`, proving `(FRC1)`.

