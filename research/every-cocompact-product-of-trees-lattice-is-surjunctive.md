---
rg: 2
id: every-cocompact-product-of-trees-lattice-is-surjunctive
kind: claim
title: Every cocompact lattice in the automorphism group of a product of two regular trees is surjunctive
distinct_from:
  strict-automaton-on-lattice-in-product-of-trees: that seeks a strict automaton on some lattice in a product of two trees; this is the positive statement for regular trees of degree at least three, and it refutes that claim on those hosts.
  radu-bmw-lattice-sofic: that is soficity of one irreducible lattice; this is only surjunctivity, for all cocompact lattices of the product.
  product-tree-lattices-in-paunescu-class-iff-f2xf2: that ties soficity of these lattices to soficity of all actions of F2 x F2; this is the surjunctivity conclusion, which that membership would give and which weaker hypotheses might also give.
  vh-lattices-surjunctive-when-a-factor-maps-faithfully: that proves surjunctivity for lattices with a surjunctive quotient faithful on a factor subgroup, excluding virtually simple lattices; this asks for all of them, virtually simple ones included.
---

**OPEN.** Let `p, q >= 3` and `L = Aut(T_p) x Aut(T_q)`. Every discrete cocompact subgroup `Gamma`
of `L` is surjunctive: every injective cellular automaton on every finite-alphabet full shift
`A^Gamma` is surjective.

**Hosts covered.**
- Radu's lattice `Gamma_R`. This would refute `radu-bmw-lattice-nonsurjunctive`.
- Burger–Mozes simple lattices and Wise's non-residually-finite square complex groups.
- Any strict automaton on `pi_1(S_R)`, which would refute this claim through
  `surjunctivity-is-a-commensurability-invariant`.

**Known cases.**
- Residually finite lattices, which are sofic.
- Lattices with a surjunctive quotient that is faithful on a factor subgroup
  (`vh-lattices-surjunctive-when-a-factor-maps-faithfully`, for torsion-free VH lattices).

**Route.** `product-tree-lattices-surjunctive-via-envelope-transfer` reduces this claim
to one residually finite group, `C_2^(*p) x C_2^(*q)`, for the measured-controlled property. That
route does not pass through soficity of any lattice.

## Attempts

- 2026-09-17 (swarm-0917-w5-gs-decomp-new). **Envelope induction.**
  - *Proved.* `measured-controlled-surjunctivity-is-envelope-invariant` reduces the claim to
    `products-of-two-virtually-free-groups-controlled-surjunctive`.
  - *Where it stops.* That prerequisite is open.
    - Its relative-entropy proof needs `F_2 x F_2 ∈ 𝒮`, which gives the stronger soficity
      conclusion here directly.
    - Periodizing the homogeneous base sees only finite `L`-sets (Attempts of that node).
    - What is needed is a measured Garden-of-Eden argument that builds no finite model of the base.
