---
rg: 2
id: compressing-letter-joins-whole-coset-blocks
kind: claim
title: A compressing letter maps each coset block into a single block, so coset percolation has no finite clusters
invalidates:
  - wreath-atoms-from-finite-coset-clusters
distinct_from:
  wreath-lamp-corner-is-coset-percolation: that is the exact spectral model for lamp corners; this describes how one compressing letter connects its blocks
---

**ESTABLISHED.** In the model `wreath-lamp-corner-is-coset-percolation`, let
`S` generate `Gamma` and let `t` satisfy `t Gamma t^(-1) <= Gamma`, with index
`m = [Gamma : t Gamma t^(-1)]`.

1. Each right coset block `Gamma h` is a copy of `Cay(Gamma, S)`: infinite
   and connected.
2. `t` sends the whole block `Gamma h` into the single block `Gamma t h`,
   onto the subset `(t Gamma t^(-1)) t h`. Each block receives `t`-edges from
   exactly `m` blocks. So the block digraph has out-degree `1` and in-degree
   `m`.
3. Every cluster of `1_U X 1_U`, for `X` supported on `S`, `t` and their
   inverses, is a union of infinite blocks. There are no finite clusters. So
   any atom must come from compactly supported eigenvectors on infinite
   clusters.
