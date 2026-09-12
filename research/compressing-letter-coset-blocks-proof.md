---
rg: 2
id: compressing-letter-coset-blocks-proof
kind: route
title: Push t past Gamma using t gamma = (t gamma t^-1) t
target: compressing-letter-joins-whole-coset-blocks
requires: []
---

Left translation by elements of `Gamma` preserves `Gamma h`, and
`gamma h -> gamma` identifies the block with `Cay(Gamma, S)`. For `gamma` in
`Gamma`, `t gamma h = (t gamma t^(-1)) t h` lies in `Gamma t h`. So the whole
block maps into one block, onto `(t Gamma t^(-1)) t h`. The preimage blocks
of `Gamma t h` correspond to the cosets of `t Gamma t^(-1)` in `Gamma`, and
there are `m` of them.
