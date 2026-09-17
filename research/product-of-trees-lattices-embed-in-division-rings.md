---
rg: 2
id: product-of-trees-lattices-embed-in-division-rings
kind: claim
title: Every torsion-free discrete group of automorphisms of a product of two locally finite trees has group rings inside division rings over every division ring, Burger--Mozes simple lattices included
distinct_from:
  some-simple-lattice-in-a-product-of-trees-is-left-orderable: that asks for one left-orderable simple lattice, which would give unique products and the zero-divisor property for that lattice only; this proves division-ring embeddability for every torsion-free lattice with no orderability input.
  product-tree-lattices-in-paunescu-class-iff-f2xf2: that concerns the Paunescu approximation class of such lattices; this is an algebraic statement about their group rings, in every characteristic.
  fsp-graph-of-rings-and-linnell-extension-imports: that is the general graph-of-rings import for locally indicable vertex groups; this identifies product-of-trees lattices as graphs of free groups, where the quotient graph has loops, so the non-separating case omitted in the source is needed.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this adds a class, containing finitely presented simple non-residually-finite groups, to its known cases.
---

**ESTABLISHED** by [[product-of-trees-lattices-embed-in-division-rings-proof]]. Not yet independently re-derived.

Let `T_1`, `T_2` be locally finite trees and `Gamma <= Aut(T_1) × Aut(T_2)` a torsion-free discrete subgroup, not
necessarily cocompact. Then for every division ring `k`, in every characteristic, `k[Gamma]` embeds in a division
ring. In particular `k[Gamma]` has no zero divisors and `M_n(k[Gamma])` is directly finite.

More generally the same holds for the fundamental group of any graph of free groups.

**Consequences for the zero-divisor conjecture.**
- The class contains the Burger--Mozes finitely presented torsion-free simple lattices
  (`burger-mozes-simple-lattices-are-highly-transitive`). It also contains Wise's non-residually-finite VH-complex
  groups and every irreducible torsion-free lattice in a product of two trees.
- These groups are:
  - not residually finite (the simple ones), so not virtually special, not linear, and outside every `CS(u,d,p)`;
  - not elementary amenable;
  - not known to have unique products.

  So this is a class of groups satisfying the conjecture over every field that is not among the known cases
  recorded in `kaplansky-zero-divisor-conjecture`.
- **Relation to the literature.** Once the lattice is written as a graph of free groups, the conclusion is an
  instance of the Fisher--Sanchez-Peralta graph corollary (item 6 of `fsp-graph-of-rings-and-linnell-extension-imports`).
  The quotient graphs have loops, and the source omits the proof of the non-separating case. What is new here is
  the reduction to graphs of free groups, the loop case proved in full, and the application to the simple lattices.
- **Class-killing obstruction for hosts.** No lattice in a product of two trees, and no graph of free groups, is a
  zero-divisor host over any field. A search for zero divisors, or for non-unique-product supports as zero-divisor
  witnesses, on `T_4 × T_4` or `T_4 × T_6` lattices cannot succeed.
- The obstruction does not say whether these lattices have unique products. It says a failure of unique products
  there never produces a zero divisor.
