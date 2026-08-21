---
rg: 2
id: higman-occurrence-separation-proof
kind: route
title: Pull every image equality back through the injective Higman map
target: higman-embedding-preserves-occurrence-coset-separation
requires: []
artifacts:
  - research/artifacts/relative-small-cancellation-occurrence-support-2026-08-21.md
---

**Established by citation and injectivity.**  Wagner, *Malnormal Subgroups of
Finitely Presented Groups*, arXiv:2404.00841v2, Theorem A gives the stated
embedding and properties; conditions (C1)--(C2) following Corollary B identify
CEP with `(HOC2)`.

If image left cosets collide, then

```text
i(g)^(-1)i(g')=i(h),  h in H_X.
```

Injectivity gives `g^(-1)g'=h`, so the source cosets already collided.  The
right-coset calculation is identical.  If image double cosets collide, an
equality

```text
i(a p_0 b)=i(a' p_1 b')
```

pulls back to the same equality in `G`, contradicting `(HOC1)`.

For a finite source offset set `D`, choose words in the finite generating set
of `A` for the finitely many elements `i(D)` and take their maximum length.
This constant is independent of the number of virtual occurrences.  CEP gives
the normal-closure identity directly.

