---
rg: 2
id: finite-packet-holonomy-cuts-the-multiplicity-simplex
kind: claim
title: Finite packet holonomy cuts rank feasibility to an orbit simplex
distinct_from:
  finite-packet-functoriality-has-positive-regular-profile: that exhibits a positive compatible profile for bare restriction and conjugacy data; this computes the complete fixed simplex after specified cycle holonomy and shows how its orbit count reduces the rank degrees of freedom.
  atlas-a4-context-types-live-in-fixed-rational-polytope: that is a construction-specific Atlas context classification; this is the abstract finite permutation-holonomy theorem for any semisimple packet network.
artifacts:
  - research/artifacts/property-t-free-rank-polytope-holonomy-integration-2026-08-25.md
---

Let a finite connected graph carry one normalized `s`-sector packet
multiplicity state `p_v in Delta_(s-1)` at every vertex.  Suppose every
oriented edge `e:v->w` transports irreducible types by a permutation
`sigma_e in S_s`, so exact transport says

```text
p_w=P_(sigma_e)p_v.                                   (HRS1)
```

Choose a base vertex.  The permutations around based cycles generate a
finite holonomy group `H<=S_s`.  In the closed normalized-state relaxation,
consistent states on the whole network are in bijection with

```text
Delta_(s-1)^H={p in Delta_(s-1): hp=p for every h in H}. (HRS2)
```

Finite-dimensional packets give the rational/divisibility points of this
simplex, and every rational fixed state is realized after a common
amplification.  After transporting all selector reads to the base, let `L`
be their combined affine rank map.  Its coefficients are rational packet
rank fractions.  The closed feasible rank envelope is the rational polytope

```text
P_(Gamma,H)=L(Delta_(s-1)^H).                         (HRS3)
```

If `H` has `t` orbits on the sector set, its fixed simplex has dimension
`t-1`: a state is constant on each orbit and is determined by the total mass
assigned to the `t` orbits.  In particular, transitive holonomy forces

```text
p=(1/s,...,1/s).                                      (HRS4)
```

For a selector with sector fingerprints `q_alpha`, one row then has the
forced rank

```text
q_bar=(1/s)sum_alpha q_alpha,
delta >= 2|r-q_bar|.                                 (HRS5)
```

More generally, the distance and rational-separator bounds of
`finite-packet-rank-polytope-is-complete` apply with the smaller polytope
`(HRS3)`.  Holonomy therefore strengthens rather than weakens a rank
obstruction: it replaces the full multiplicity simplex by its fixed
subsimplex.
