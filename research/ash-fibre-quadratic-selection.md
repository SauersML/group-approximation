---
rg: 2
id: ash-fibre-quadratic-selection
kind: claim
title: Every simple ASH inductive system eventually selects a near projection with each prescribed stage trace profile
distinct_from:
  stw99-problem-xxiv-ash-ranks-almost-occur: that asks for limiting affine rank approximation; this is its equivalent finite-stage degree-two moment selection problem, with all irreducible fibres tested and all matrix normalizations fixed.
artifacts:
  - research/artifacts/ash-rank-quadratic-selection-2026-09-11.md
---

Let `(A_n,phi_nj)` be an injective unital inductive system of separable
unital subhomogeneous C*-algebras with simple non-elementary limit `A` and
nonempty `T(A)`. For every `n`, `h in (A_n)_+`, and `epsilon>0`, there are
`j>=n`, `m>=1`, and a positive contraction `b in M_m(A_j)` such that every
irreducible representation `pi:A_j->M_d(C)` satisfies, with
`B=pi^(m)(b)` and `H=pi(phi_nj(h))`,

```text
|Tr_(md)(B)-Tr_d(H)| < epsilon d,
Tr_(md)(B-B^2)       < epsilon d.
```

This assertion is **open**. Its equivalence to STW XXIV is proved by
`rank-density-is-quadratic-trace-selection`; the implication is not a proof
that the desired selections exist. No dimension-growth hypothesis is
present. A valid negative witness must retain every later stage, matrix
size, and positive contraction in the quantified obstruction (5) of the
artifact.

## Attempts

- Extending the AH construction over a recursive subhomogeneous attachment
  requires one continuous positive matrix field satisfying the prescribed
  boundary equations. Independent fibrewise near projections do not glue,
  and a general positive extension need not preserve the quadratic defect
  bound. No dimension-free solution of this extension problem was obtained.
- Finitely many extreme limit traces cannot certify failure: Section 4 of
  the artifact constructs simultaneous near projections at any such finite
  set using the diffuse GNS factors and Kaplansky density. Any negative
  certificate must keep the bad fibre dependent on the chosen global
  element and must persist through every later stage and matrix size.
