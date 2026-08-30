---
rg: 2
id: stw99-xcix-zero-distance-z-saturated-limit
kind: claim
title: Zero-distance unital XCIX pairs have a common Z-saturated limit
artifacts:
  - research/artifacts/stw99-xcix-quantitative-audit-2026-08-30.md
distinct_from:
  stw99-xcix-z-stability-is-kk-closed: closedness fixes one ambient algebra and one limit algebra; here both coordinate algebras may vary and the conclusion concerns their common norm ultraproduct.
---

Let `omega` be a free ultrafilter.  For every `n`, let `A_n,B_n` be separable
C*-subalgebras of one `C_n`.  Suppose that `A_n` is unital (the nearby
`B_n` need not be unital) and

```text
A_n is Z-stable,
lim_(n->omega) d_KK(A_n,B_n)=0.
```

Their common norm ultraproduct

```text
P=prod_omega A_n=prod_omega B_n
```

is **Z-saturated**: for every separable C*-subalgebra `S subset P`, there is
a unital embedding

```text
Z -> P intersect S'.
```

In particular, if uniform Kadison--Kastler openness fails through counterexamples
with unital source algebras, every vanishing-distance counterexample sequence
still converges to a maximally locally Z-absorbing object.  This does not say
that `P` is tensorially Z-stable; nontrivial ultraproducts need not tensorially
absorb a strongly self-absorbing algebra.
