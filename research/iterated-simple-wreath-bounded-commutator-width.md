---
rg: 2
id: iterated-simple-wreath-bounded-commutator-width
kind: claim
title: Iterated wreath products of nonabelian simple transitive groups of bounded degree are perfect, 2-generated up to a bound, and have uniformly bounded commutator width
distinct_from:
  nikolov-segal-uniform-commutator-width: that is the general bound for d-generator finite groups; this applies it to the towers, after bounding their number of generators independently of depth.
  relator-width-bounded-over-simple-iterated-wreath-products: that uses this width bound to bound relator width over the towers; this is the finite group theory input alone.
---

**ESTABLISHED.** Fix `m`. Let `W = T_1 wr ... wr T_d` be an iterated permutational wreath product
acting on a rooted tree, with each vertex group `T_i <= Sym(m_i)`, `m_i <= m`, transitive and nonabelian
simple.
1. `W` is perfect.
2. The bottom layer `B = T_d^(k)`, the labels at the vertices just above the leaves, is the unique minimal
   normal subgroup of `W`, and `W/B` is the tower of depth `d - 1`.
3. `d(W) <= delta(m) := max(2, floor(log_2 m!))`, for every depth.
4. There is `c(m)` such that every element of `W` is a product of at most `c(m)` commutators, for every
   depth.

Credit: items 1--3 are elementary or immediate from the imports; item 4 is Nikolov--Segal applied to
item 3. No claim of novelty.

Derivation: `iterated-simple-wreath-bounded-commutator-width-proof`.
