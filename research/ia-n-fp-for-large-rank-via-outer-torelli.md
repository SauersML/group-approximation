---
rg: 2
id: ia-n-fp-for-large-rank-via-outer-torelli
kind: route
title: "Eventual finite presentability of the Out(F_n) Torelli groups gives the same for IA_n"
target: ia-automorphism-groups-fp-for-large-rank
requires:
  - outer-torelli-groups-fp-for-large-rank
  - ia-n-fp-iff-outer-torelli-fp
---

If `T_n` is finitely presented for all `n >= n_0`, then by the rank-by-rank
equivalence `ia-n-fp-iff-outer-torelli-fp`, so is `IA_n` for all
`n >= max(n_0, 2)`.

This route and `outer-torelli-fp-for-large-rank-via-ia-n` form a dependency cycle on
purpose: the two answer claims are equivalent. The least fixpoint never fires a
cycle, so neither claim establishes itself; do not delete either direction.
