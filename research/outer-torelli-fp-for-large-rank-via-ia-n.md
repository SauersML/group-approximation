---
rg: 2
id: outer-torelli-fp-for-large-rank-via-ia-n
kind: route
title: "Eventual finite presentability of IA_n gives the same for the Out(F_n) Torelli groups"
target: outer-torelli-groups-fp-for-large-rank
requires:
  - ia-automorphism-groups-fp-for-large-rank
  - ia-n-fp-iff-outer-torelli-fp
---

If `IA_n` is finitely presented for all `n >= n_0`, then by the rank-by-rank
equivalence `ia-n-fp-iff-outer-torelli-fp`, so is `T_n` for all
`n >= max(n_0, 2)`.

This route and `ia-n-fp-for-large-rank-via-outer-torelli` form a dependency cycle
on purpose: the two answer claims are equivalent. The least fixpoint never fires a
cycle, so neither claim establishes itself; do not delete either direction.
