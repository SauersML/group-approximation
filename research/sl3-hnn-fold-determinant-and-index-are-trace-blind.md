---
rg: 2
id: sl3-hnn-fold-determinant-and-index-are-trace-blind
kind: claim
title: Determinant and additive Fredholm index are blind to the SL3 HNN fold trace
artifacts:
  - research/artifacts/sl3-joint-determinant-index-audit-2026-08-21.md
distinct_from:
  source-hecke-data-leave-projective-square-free: that varies the mixed trace-square coefficient among tracial extensions while preserving scalar source Hecke data; this is an exact finite-matrix calculation on the marked commutator itself.
  odd-congruence-native-sector-has-defect-only-gap: that audits determinant parity for the balanced two-projection native lamp and proves a gap on one exact congruence sector; this treats the general HNN commutator and additive index before any native involution reduction.
---

For arbitrary finite-dimensional unitaries `T,H`,

```text
det([T,H])=1.                                             (JDT1)
```

For every `d>=2` there are `T_d,H_d in U(d)` such that

```text
det([T_d,H_d])=1,       tr_d([T_d,H_d])=0.               (JDT2)
```

One may take `H_d` to be the cyclic shift and choose diagonal `T_d` so the
successive diagonal ratios are a scalar multiple of all `d`th roots of
unity, with scalar chosen to make their product one.

Likewise every additive Fredholm index of a square finite matrix is zero,
and the relative index of `P` and `HPH^*` is zero because the projections
have equal rank.  Therefore determinant, parity, or an additive index of
the marked HNN carrier cannot force `|tr([T,H])|` away from zero.  Such a
bound must use the global approximate `A` relations and joint Hecke-
multiplicity coherence, not these invariants alone.
