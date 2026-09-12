---
rg: 2
id: stw99-xcix-central-copy-transfer-bound
kind: claim
title: Transporting a central strongly self-absorbing copy incurs a fixed square-root loss
artifacts:
  - research/artifacts/stw99-xcix-quantitative-audit-2026-08-30.md
---

Let `d(A,B)<gamma` with `0<gamma<1/12600000`, let `D` be strongly
self-absorbing, and suppose an
embedding `psi:D -> A` is given.  For finite subsets `Y` of the unit ball of
`D` and `X` of the unit ball of `B`, choose `a_x` in the unit ball of `A`
with `||a_x-x||<gamma`.  There is an embedding `phi:D -> B` such that, for
every `x in X` and `y in Y`,

```text
||[phi(y),x]||
  < ||[psi(y),a_x]|| + 304 sqrt(gamma) + 2 gamma.
```

Thus the stated estimate does not by itself certify the arbitrarily central
embeddings required for D-stability at one fixed positive `gamma`.  This is
an additive upper-bound loss, not a lower bound on the centrality of the
embedding actually selected.
