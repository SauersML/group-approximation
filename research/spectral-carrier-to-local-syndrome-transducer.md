---
rg: 2
id: spectral-carrier-to-local-syndrome-transducer
kind: claim
title: A marked spectral carrier can be compiled into bounded-overlap local index syndromes
artifacts:
  - research/artifacts/universal-hyperlinearity-audit-2026-08-18.md
distinct_from:
  extensive-cosystolic-index-defect: that is the final presentation-level energy obstruction; this isolates the only nonautomatic local-to-global compiler after marked separation has already supplied positive spectral density
---

Construct a finite presentation

```text
P=<S | R>
```

a word `z` nontrivial in `P`, a threshold `alpha>0`, and constants

```text
0<theta<1,  gamma>0,  L>0,  D>=1,  B>=1
```

with the following uniform property.  For every matrix dimension `d` and every
unitary `S`-tuple `U` with sufficiently small relator defect and

```text
||z(U)-1||_2 >= alpha,
```

let

```text
Q=1_{|z(U)-1| >= theta alpha}.
```

There are finitely many nonzero local carriers `P_j`, each of rank at most
`B`, carrying nonzero integer/rank index syndromes and equipped with relator
neighborhoods `N(j) subset R`, such that

```text
sum_j rank(P_j)/d >= gamma tau_d(Q),                  (mass transfer)

rank(P_j)/d
 <= L sum_(r in N(j)) ||r(U)-1||_2^2,                (local payment)
```

and every relator belongs to at most `D` of the neighborhoods `N(j)`.

The point is deliberately compiler-like.  The global mark has already been
turned into a macroscopic spectral region by
`marked-hs-separation-forces-spectral-density`; this claim asks only for a
local incidence structure which labels a fixed fraction of that region by
stable syndromes and charges those labels to bounded-overlap relator tests.

## Attempts

- **qLDPC/cosystolic decoder viewpoint.** Treat the spectral subspace `Q C^d`
  as the message mass and seek a bounded-degree Tanner/chain-complex map whose
  violated local checks carry a rank-one or bounded-rank index label.  The
  needed theorem is not merely expansion of a classical syndrome: the map from
  the unitary tuple to the local labels must be stable under normalized-HS
  perturbation.
- **Spectral slicing first.** Work on dyadic spectral arcs of `z(U)` away from
  `1`; `marked-hs-separation-forces-spectral-density` guarantees one fixed
  collection of arcs has positive total rank.  Try to attach each arc to a
  local Bott/Fredholm chart so bounded rank is automatic and expansion is used
  only to route, not create, mass.
- **PCP gap amplification.** Compile each local index chart into a constant
  number of relator tests and then use a bounded-degree expander replacement.
  `bounded-overlap-syndrome-energy-accounting` shows that once local payment
  survives this compilation, no further analytic argument is needed.
- **What does not suffice.** A positive-density topological index without the
  displayed local-payment inequality still obstructs repair rather than the
  existence of approximate representations; that dead end remains excluded.
