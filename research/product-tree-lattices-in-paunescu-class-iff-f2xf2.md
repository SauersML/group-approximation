---
rg: 2
id: product-tree-lattices-in-paunescu-class-iff-f2xf2
kind: claim
title: A cocompact lattice in the automorphism group of a product of two regular trees has only sofic actions iff F2 x F2 does
distinct_from:
  paunescu-class-is-measure-equivalence-invariant: that is the general invariance theorem; this is its instantiation on products of two trees, where it ties every irreducible tree lattice to one residually finite group
  radu-bmw-lattice-embeds-in-titz-witzel-kernel: that imports the structure of Radu's lattice; this puts that lattice, with all other cocompact lattices of the same product, in one class with F2 x F2
artifacts:
  - research/artifacts/paunescu-class-measure-equivalence-2026-09-12.md
---

**ESTABLISHED (unreviewed).** Let `p, q >= 3`, `T_p`, `T_q` regular trees and
`L = Aut(T_p) × Aut(T_q)`. For every cocompact lattice `Γ <= L`:

```text
Γ ∈ 𝒮   iff   F_2 × F_2 ∈ 𝒮,
```

where `𝒮` is Păunescu's class of groups all of whose p.m.p. actions are sofic.

Consequences.

1. If `F_2 × F_2 ∈ 𝒮`, every cocompact lattice in a product of two regular trees
   of degrees at least `3` is sofic. This includes Radu's BMW lattice
   (`radu-bmw-lattice-sofic`) and the fundamental groups of one-vertex complete
   square complexes, among them Wise's non-residually-finite examples and many
   Burger--Mozes groups.
2. If one such lattice is not sofic, `F_2 × F_2` has an essentially free
   nonsofic p.m.p. action, obtained by the explicit transfer of
   `paunescu-class-is-measure-equivalence-invariant`. `F_2 × F_2` is residually
   finite and linear, and has the Haagerup property, so it has no infinite Kazhdan
   subgroup and the Kun--Thom mechanism cannot produce such an action directly.

So the soficity question for irreducible lattices in products of trees is at most
as hard as the soficity of all actions of one residually finite group.

Proof in `product-tree-lattices-paunescu-class-proof`.
