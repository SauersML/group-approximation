---
rg: 2
id: free-group-minimal-overgroup-rank-is-fox-rank-citation
kind: route
title: Import Theorem 3.12 of Jaikin-Zapirain's L2-subgroup rigidity paper and translate its Betti number into the Fox rank
target: free-group-minimal-overgroup-rank-is-fox-rank
requires:
  - linnell-dimension-equals-skew-field-rank
  - lueck-dimension-additivity-cofinality-and-induction
---

Literature import. Source: A. Jaikin-Zapirain, *Free groups are L2-subgroup
rigid*, arXiv:2403.09515v2 (3 Feb 2026), read from the arXiv PDF on
2026-09-19. The same paper is imported for Corollary 1.2 in
`compressed-subgroups-of-free-groups-are-l2-independent-citation`.

Imported verbatim (quoted in full in the target):
- Theorem 3.12 (p. 15), for `K = Q`;
- the definition of `π̄` (p. 15) and of `β^{k[G]}_i` through the universal
  division ring `D_{k[G]}` (p. 6);
- the identification `D(F) ≅ D_{Q[F]}` as `Q[F]`-rings (p. 7), from Hughes'
  uniqueness theorem.

The translation from `β_1(I_{Q[F]}/^F I_{Q[H]})` to `p − rk(A)` is a
three-line exact-sequence computation. It is written out in the target. The
passage from `D(F)`-rank to `N(F)`-rank uses the two required nodes, as in §3
of `fpbs-sandwich-cost-fox-rank-lower-bound-proof`.

Not re-read: [Mal80], [Hug70], [Lin93] and the proof of Theorem 3.12, whose
second inequality (14) rests on Theorem 1.1 of the paper (free groups are
`L2`-subgroup rigid).
