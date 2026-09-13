---
rg: 2
id: fp-direct-limit-of-quotients-equals-a-finite-stage-proof
kind: route
title: The finitely many normal generators of the kernel appear at a finite stage
target: fp-direct-limit-of-quotients-equals-a-finite-stage
requires: []
---

Let `S` be a finite free basis of `F`. Finite presentability does not depend on
the finite generating set: if `G` has some finite presentation, then for the
generating set given by the images of `S`, the kernel `K` of `F -> G` is the
normal closure of a finite set `{r_1, ..., r_s}`. (This is B. H. Neumann's
observation. Express the generators of a finite presentation as words in `S`
and conversely; Tietze transformations give a finite presentation on `S`.)

Each `r_j` lies in `K = U_i K_i`, so `r_j in K_{i_j}` for some `i_j`. The chain is
increasing, so for `i >= max_j i_j` all `r_j` lie in `K_i`. `K_i` is normal, so
`K = << r_1, ..., r_s >> <= K_i <= K`, and `K = K_i`.
