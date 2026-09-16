---
rg: 2
id: one-ended-hyperbolic-groups-contain-surface-or-rigid
kind: claim
title: Every one-ended hyperbolic group contains a surface subgroup or an infinite quasiconvex rigid subgroup
distinct_from:
  wilton-no-2-torsion-surface-or-rigid-subgroup: that is Wilton's Corollary 6.4, which assumes no 2-torsion; this is the same dichotomy for every one-ended hyperbolic group, including those with 2-torsion
  one-ended-hyperbolic-groups-contain-surface-subgroups: that demands a surface subgroup; this also accepts an infinite quasiconvex rigid subgroup, so it is weaker
  hyperbolic-finite-residual-is-torsion-free: that is about torsion in finite quotients of hyperbolic groups; this is a subgroup dichotomy which follows from it but is not known to imply it
---

**OPEN.** Let `Gamma` be a one-ended hyperbolic group. Then at least one of the following holds:

- `Gamma` contains a subgroup isomorphic to the fundamental group of a closed surface with
  `chi < 0`;
- `Gamma` contains an infinite quasiconvex subgroup which admits no nontrivial splitting over a
  finite or virtually cyclic subgroup.

The root claim implies this one trivially. With `rigid-hyperbolic-groups-contain-surface-subgroups`
it implies the root. So the root is equivalent to the conjunction of the two.

## Attempts

- **Without 2-torsion.** This is Wilton's Corollary 6.4, imported as
  `wilton-no-2-torsion-surface-or-rigid-subgroup`. The only obstruction is 2-torsion.
- **Pass to a finite-index subgroup.**
  - The route `surface-or-rigid-via-virtual-torsion-freeness` reduces the claim to
    `hyperbolic-finite-residual-is-torsion-free`, that is, to hyperbolic groups being virtually
    torsion-free.
  - Universally over hyperbolic groups, that is equivalent to residual finiteness
    (`universal-hyperbolic-vtf-iff-rf`), a well-known open problem.
  - Asking only for a finite-index subgroup without 2-torsion is no easier universally. Sketch,
    with second-hand inputs:
    - Dehn filling `g^{2n}` in a non-elementary hyperbolic group gives a hyperbolic quotient in
      which `g^n` has order `2`.
    - A finite-index subgroup of the quotient without 2-torsion misses `g^n`, so it is proper.
    - So every non-elementary hyperbolic group would have a proper finite-index subgroup, and by
      Kapovich--Wise all hyperbolic groups would be residually finite.
- **Remove the 2-torsion hypothesis from the hierarchy.**
  - Wilton's proof of Corollary 6.4 uses the torsion hypothesis only through Louder--Touikan's
    finite hierarchy. Its other inputs, Remark 6.2 and Theorem 6.1, are stated with no torsion
    hypothesis.
  - Wilton writes that the 2-torsion restriction "is technical, and conjecturally can be removed".
  - Louder--Touikan was not read at source here (arXiv downloads reset, 2026-09-16), so the place
    where their argument uses the absence of 2-torsion was not located. No route through a finite
    hierarchy was written, because Remark 6.2 depends on how the hierarchy is built, and that
    construction was not checked.
