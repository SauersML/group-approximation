---
rg: 2
id: nonhyperlinear-from-three-word-atlas-gap
kind: route
title: A uniform gap for two pair-cubes and collision 19243 rules out hyperlinearity directly
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
  - atlas-a4-three-word-amplified-gap
---

Let `Q=L_(F_2)(1,2)^x`, the explicit binary Leavitt unit group used throughout
the regular-atlas route, and suppose for contradiction that `Q` is hyperlinear.
Use the **necessity** construction behind
`leavitt-regular-atlas-hyperlinearity-criterion`: pull a separating
hyperlinear microstate sequence of `Q` back through the two finite A8 charts
and regularize the finite-factor restrictions.  As in the existing A4
holonomy route, this canonical choice can be diagonalized so every fixed
kernel word needed below has normalized-HS defect `o(1)`.

The packet claim says the two tree words at indices `6910,6940` are genuine
kernel words, and `atlas-word-19243-is-kernel-relation` says the same for
`q_19243`.  Hence on the resulting regular relative-unitary sequence `U_n`,

```text
||u(U_n)-1||_2 -> 0,
||v(U_n)-1||_2 -> 0,
||q(U_n)-1||_2 -> 0.
```

But `atlas-a4-three-word-amplified-gap` supplies one `epsilon>0`, independent
of the external multiplicity, for which the sum of the three squared defects
is always at least `epsilon`.  Contradiction.

Therefore `Q` is not hyperlinear.  This route bypasses simultaneous A4
exactification, thirty-context holonomy synchronization, packet-commutator
collapse, and S3 covariance reconstruction.  Its sole new analytic theorem is
a uniform three-word Hilbert--Schmidt gap for one relative unitary.
