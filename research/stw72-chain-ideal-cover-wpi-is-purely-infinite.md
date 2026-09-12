---
rg: 2
id: stw72-chain-ideal-cover-wpi-is-purely-infinite
kind: claim
title: Chain-ideal covers collapse weak pure infiniteness to pure infiniteness
distinct_from:
  stw72-chain-ideal-wpi-is-purely-infinite: that theorem requires the entire closed ideal lattice to be linearly ordered; here only the members of an arbitrary ideal cover have linearly ordered internal ideal lattices, while the ambient lattice can contain infinite antichains.
  stw72-transfinite-simple-layer-wpi-is-purely-infinite: that theorem builds upward along one well-ordered filtration with simple successor quotients; here the cover need not be nested or well ordered and no member need contain a nonzero simple ideal.
  stw72-scattered-primitive-spectrum-wpi-is-purely-infinite: a chain-ideal cover need not give even one isolated primitive point; the explicit rational-cut graph example has no minimal nonzero ideal and hence has non-scattered primitive spectrum.
artifacts:
  - research/artifacts/stw72-chain-ideal-cover-collapse-audit-2026-08-30.md
---

Let `A` be a C-star algebra and let `(I_lambda)_(lambda in Lambda)` be a
family of closed two-sided ideals such that

```text
A = closure(sum_(lambda in Lambda) I_lambda).          (1)
```

Assume that the closed two-sided ideals of each `I_lambda` are linearly
ordered by inclusion.  If `A` is weakly purely infinite, then `A` is purely
infinite.

Equivalently, the weak-to-plain implication in Problem LXXII holds when
`Prim(A)` has an arbitrary open cover whose corresponding ideals have
linearly ordered ideal lattices.  The cover is not required to be finite,
locally finite, nested, or countable.  No separability, nuclearity,
unitality, exactness, or separation hypothesis is imposed.
