---
rg: 2
id: stw74-gapless-compression-proof
kind: route
title: Turn any compression gap into a projection by functional calculus
target: stw74-projectionless-corner-forces-gapless-compressions
requires: []
---

Fix `xi` with `a=a_xi!=0`.  Suppose that zero were not an accumulation point
of the nonzero spectrum of `a`.  Then for some `epsilon>0`,

```text
sigma(a) subset {0} union [epsilon,infinity).
```

The function which is zero at zero and one on the nonzero spectrum is
continuous on `sigma(a) union {0}`.  Nonunital continuous functional calculus
therefore produces

```text
q = 1_(0,infinity)(a) in C*(a) subset D.
```

This is a nonzero projection, contradicting projectionlessness of `D`.
Nothing in the argument depends on whether `p` is finite, infinite, full, or
properly infinite, so the same obstruction applies to the stabilized
projection supplied by `stw74-counterexamples-are-unstably-projectionless`.
