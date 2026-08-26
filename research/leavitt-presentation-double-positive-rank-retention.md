---
rg: 2
id: leavitt-presentation-double-positive-rank-retention
kind: claim
title: The Shulman-induced unstable representation pairs of the Leavitt presentation double admit a positive-rank sector that is almost reducing, almost trivial on the kernel and retains a quotient element
distinct_from:
  intertwiner-retention-makes-leavitt-quotient-hyperlinear: that is the established implication from such a sector to hyperlinearity; this is the open existence statement, the single missing theorem of the presentation-double program.
  binary-leavitt-unit-group-hyperlinear: that asks for hyperlinearity of the whole unit group of the binary Leavitt algebra; this asks for a specific analytic sector inside explicit finite-dimensional intertwiner spaces for the rank-four elementary subgroup, which would prove hyperlinearity of that subgroup only.
  mf-trace-gap-defect-ratio-models: that asks for microstates with a dimension-versus-defect profile in the MF-to-hyperlinear lane; this asks for a retained sector inside Hilbert--Schmidt spaces of exact representations, where the defect is an operator-norm instability of restriction, not a multiplicative defect.
artifacts:
  - research/artifacts/hyperlinear-nonsofic-attack-notebook-2026-08-26.md
---

OPEN.  With `Q = EL_4(L_(F_2)(1,2)) = F/K`, `P = F *_K F`, and the exact
pairs `u_n, v_n : F -> U(d_n)` of
`leavitt-presentation-double-forces-restriction-instability`, there exist
subspaces `W_n <= HS(C^(d_n))` satisfying (IR1)--(IR3) of
`intertwiner-retention-makes-leavitt-quotient-hyperlinear`.

**Spectral form.**  For `K_m = {k_1, ..., k_m}` exhausting `K` put
`A_(n,m) = sum_j (Pi_n(k_j) - 1)^*(Pi_n(k_j) - 1)`; the vector
`xi_n = 1/sqrt(d_n)` has `<A_(n,m) xi_n, xi_n> = sum_j ||u_n(k_j) - v_n(k_j)||_2^2 -> 0`.
The claim asks for `m(n) -> infinity`, `eta_n -> 0` with the low-energy sector
`1_[0, eta_n](A_(n, m(n)))` of rank `r_n -> infinity`, almost reducing
`Pi_n(F)` and displacing `f_0` by a fixed amount, both measured in its own
normalized norm.

## Attempts

- **One low-energy direction is not enough.**  `<A xi, xi> -> 0` gives one
  almost-invariant direction; a rank-one sector has zero normalized profile
  inside `d_n^2`, and after renormalizing on it nothing controls the
  reducing condition.  The kernel `K` is a normal subgroup of a free group
  (typically free of infinite rank) and has no property (T), so no spectral
  gap produces a Kazhdan-corner extraction.
- **Exact sectors are forbidden.**  The zero-energy space
  `1_{0}(A_(n,m))` for the full `K` is the exact intertwiner space, which
  carries a trivial representation of `Q`
  (`normal-kernel-restriction-rigidity-for-map-free-quotients`), so (IR3)
  fails there; the sector must be a shrinking annulus `1_[a_n, b_n]` with
  `0 < a_n < b_n -> 0`, retaining the unstable mass just above zero.
- **The missing estimate.**  Almost-reduction of an annulus needs a
  commutator bound `||[A_(n,m), Pi_n(f)]||_2 <= C_(m,f) . kernel error`, which
  would follow from approximately conjugation-invariant finitely supported
  weights on `K` under a finite `F`-window -- a Folner-type request for the
  conjugation action of `F` on `K`, which has no reason to hold.  Property
  (T) of `Q` might control conjugation orbits indirectly; no inequality
  achieving this is recorded.
- **Constraint from the model decomposition.**  Any hyperlinear model of `Q`
  obtained this way must represent `Q` non-amenably and without
  finite-dimensional subrepresentations
  (`finitely-generated-map-groups-are-residually-finite`), consistent with
  the requirement that the retained sector be genuinely asymptotic.
