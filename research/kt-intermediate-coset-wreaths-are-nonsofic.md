---
rg: 2
id: kt-intermediate-coset-wreaths-are-nonsofic
kind: claim
title: Every binary coset wreath over a subgroup between Gamma and G missing the normal closure is nonsofic
distinct_from:
  kun-thom-nonsofic-wreath: that is Kun--Thom Theorem A for the single index set G/Gamma; this extends the conclusion to every intermediate index set G/K with Gamma <= K and K not containing the normal closure of Gamma, by the same Theorem 4.1 argument.
  normal-closure-fixes-gamma-fixed-algebra: that says the normal closure acts trivially on the Gamma-fixed diagonal of a sofic representation; this is a nonsoficity theorem for a family of groups.
artifacts:
  - research/artifacts/kt-wreath-double-re-unification-2026-09-11.md
---

**ESTABLISHED.**  Let `Gamma < G` be the Kun--Thom Theorem E pair and
`N = <<Gamma>>_G` its normal closure (`= EL_r(R)` by
`normal-closure-fixes-gamma-fixed-algebra`).  For every subgroup `K` with

```text
Gamma <= K <= G,        N not contained in K,
```

the binary coset wreath `W_K = (direct_sum_(G/K) Z/2Z) rtimes G` is not
sofic.  The case `K = Gamma` is Kun--Thom Theorem A.

The only inputs are Kun--Thom Theorem 4.1 for `Gamma <= G`, which uses
infranormality and property (T) of `Gamma` and of `G` but nothing about `K`,
and the fact that `Gamma` fixes the coset `K`.  In particular `K` need not be
Kazhdan or infranormal: the one-compressor ascending HNN subgroups
`<Gamma,t>` are covered.

DERIVATION
kt-intermediate-coset-wreaths-nonsofic-proof
