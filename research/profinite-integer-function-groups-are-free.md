---
rg: 2
id: profinite-integer-function-groups-are-free
kind: claim
title: "Nöbeling's theorem: the group of continuous integer-valued functions on a profinite space is free abelian"
---

Let `S` be a profinite space (a compact, Hausdorff, totally disconnected
topological space). Then the abelian group `C(S, Z)` of continuous maps
`S → Z`, with pointwise addition and `Z` discrete, is a free abelian group.

Since `Z` is discrete, `C(S, Z)` is the group of locally constant integer-valued
functions on `S`. No countability or metrizability assumption is made on `S`.

## Attempts

- Imported from the literature in
  `profinite-integer-function-groups-are-free-citation`.
- For metrizable `S`, and more generally whenever `S` is an inverse limit of a
  sequence of finite sets, freeness also follows from Lemma C of
  `research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md` §5.
  `C(S, Z)` is then the increasing union of the finitely generated pure subgroups
  of functions factoring through the finite stages.
