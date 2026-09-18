---
rg: 2
id: hermitian-edge-trace-norm-other-stab-facets-antihole-split
kind: route
title: Split the remaining full-support stable-set facets into odd-antihole rank facets and the rest
target: hermitian-edge-trace-norm-other-stab-facets
requires:
  - hermitian-edge-trace-norm-odd-antihole-facets
  - hermitian-edge-trace-norm-other-stab-facets-non-antihole
artifacts:
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/README.md
---

Lane w7-078, 2026-09-18. This is a case split with no mathematics in it. A full-support facet
`(H, a)` of `STAB(H)` that is neither a clique nor an odd hole either is (an odd antihole `C̄_n`,
`n >= 7`, with `a = 1`) or is not. The first case is
`hermitian-edge-trace-norm-odd-antihole-facets`. By the rank-perfectness of antiwebs (Wagler 2004),
`a = 1` is the only full-support facet of an odd antihole, so no antihole facet falls into the second
case. The second case is `hermitian-edge-trace-norm-other-stab-facets-non-antihole`.

The split separates the antiholes because a separate proof exists for them: coverings by cliques and
houses, and a kernel LP on the rank-one reduction. In the numerics of the target node they are also the
tightest family (`C̄_9`: ratio `1.108`).
