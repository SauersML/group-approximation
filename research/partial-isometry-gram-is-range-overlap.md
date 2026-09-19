---
rg: 2
id: partial-isometry-gram-is-range-overlap
kind: claim
title: Cross-Gram energy of partial isometries equals overlap of their final ranges
distinct_from:
  gram-branching-capacity-with-overlap: that theorem turns a given Gram penalty into a capacity inequality; this theorem identifies the penalty exactly with projection overlap when the branches are partial isometries.
  common-range-isometries-have-maximal-gram-overlap: that is the common-final-range special case; this gives the full two-range identity needed to design viable return automata.
---

Let `(M,tau)` be a finite tracial von Neumann algebra and let `S,T in M` be
partial isometries.  Write their final projections as

```text
F = S S^*,
G = T T^*.
```

Then

```text
||S^* T||_2^2 = tau(F G) = ||F G||_2^2.
```

Thus, for partial-isometry branches, vanishing incoming cross-Gram energy is
exactly asymptotic Hilbert--Schmidt orthogonality of the branch ranges.  There
is no additional phase or source-space mechanism that can cancel it.