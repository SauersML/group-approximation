---
rg: 2
id: npa-residual-rows-independent-via-unseen-freeness
kind: route
title: Read off two independent projections on coordinates no old row touches
target: npa-two-residual-rows-independent-mod-old-rows
requires:
  - npa-unseen-classes-are-free-at-level-k
  - npa-first-residual-gauge-row-closed-form
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

Take `m = r_(2k-3)`, the alternating word of length `2(k-1)-1` ending in `1`, and
the three classes `U_1 = (empty,m)`, `U_3 = ((0),m)`, `U_4 = ((1),m)`, which are
the degree-`(2k-3)` exceptional classes of the level-`(k-1)` shell.

By the first prerequisite, every row of `Phi_(k-1)` has coefficient zero on each
of `U_1, U_3, U_4`.  So the projection `pi` onto those three coordinates kills the
whole level-`(k-1)` row space, and it suffices that `pi(A_k)` and `pi(B_k)` be
independent.

The second prerequisite gives `A_k = 2 y_[U_1] - 2 y_[U_3]`, i.e.
`pi(A_k) = (2,-2,0)`.  Expanding `B_k` from the dressing form
`D_[(empty,e_j)] = (e_[empty] - e_[(1)]) tensor (e_[r_(j-1)] - e_[r_(j+1)])` and
collecting the terms of top degree gives `pi(B_k) = (2,0,-2)`.  The two vectors
are independent, so no nontrivial combination `alpha A_k + beta B_k` lies in the
level-`(k-1)` row space.

Two things this route does not establish, recorded so the hole is not double
counted.  The full six-term identity for `B_k` at lower degrees is not needed
here -- only its projection -- but it is also not verified in this graph.  And the
first prerequisite is the load-bearing one: it is asserted in the imported germ
step from an analysis of the transitions `2->3`, `3->4`, `4->5` only, and it is
where the whole upper-bound induction stops being a proof.
