---
rg: 2
id: cornulier-kazhdan-central-quotient-citation
kind: route
title: Import the group definition and reduce modulo an auxiliary prime
target: cornulier-kazhdan-groups-are-central-quotients-of-linear-groups
requires: []
artifacts:
  - research/artifacts/central-quotient-rf-exclusion-2026-09-08.md
---

Literature import, checked 2026-09-08 against Yves de Cornulier,
*Finitely presentable, non-Hopfian groups with Kazhdan's Property (T) and
infinite outer automorphism group*, Proc. Amer. Math. Soc. **135** (2007)
951--959; arXiv:math/0502140 carries the corrected version, whose 2011
erratum concerns Theorem 3.1 and is not used here.

* **Definition 2.4** specifies the groups as central quotients of
  subgroups of `GL_r(Z[1/p])`.
* **Proposition 2.7** gives property (T) and the failure of Hopficity.
* **Theorem 1.3** gives finite presentability.

Only the shape `(CN1)` is imported.

## The residual finiteness is proved here, not imported

Let `A != I` in `GL_r(Z[1/p])` and pick an entry of `A - I` that is
nonzero.  Write it as `a/p^k` with `a` a nonzero integer.  Choose a prime
`l` with `l != p` and `l` not dividing `a`.  Reduction of `Z[1/p]` modulo
`l` is a well-defined ring map because `p` is invertible mod `l`, and it
carries `GL_r(Z[1/p])` into the finite group `GL_r(Z/l)`.  The chosen
entry has nonzero image, so `A` is separated from the identity.  Hence
every subgroup of `GL_r(Z[1/p])` is residually finite.

There are infinitely many primes, so such an `l` exists.
