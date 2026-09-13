---
rg: 2
id: chain-transitive-core-has-no-transient-points
kind: claim
title: If the chain-recurrent set of a compact metric homeomorphism is chain transitive, every point is chain recurrent
artifacts:
  - research/artifacts/un-hh-extension-toeplitz-subshift-2026-09-13.md
---

Let `T` be a homeomorphism of a compact metric space `X`. Suppose `CR(T)` is chain transitive: for every `eps > 0`,
any two of its points are joined by an `eps`-chain in `X`. Then `CR(T) = X`. In particular, if `CR(T)` is a minimal
set, then `X` is that minimal set.

This is a standard Conley-theory fact, recorded here because it rules out a whole shape of example. A zero-dimensional
system with transient points has a non-minimal chain-recurrent core.

**Review (un-verify-3, 2026-09-13): PASS (standard).** Re-derived the ε-chain `x, …, T^(N−1)x, y_0, …, y_(k−1), T^(−M)x, …, x`. The junctions are `< δ` and `< 2δ = ε`. Limit sets are nonempty (compactness) and lie in `CR(T)`. A minimal set is chain transitive through its dense orbits. Standard Conley theory. `research/artifacts/un-review3-2026-09-13-part5.md` §2.
