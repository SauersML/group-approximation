---
rg: 2
id: strict-pairs-need-inverted-memory-or-positive-memory-relations
kind: claim
title: A strict automaton pair has a decoder element inverting a memory element, or positive relations in both memories
distinct_from:
  strict-left-inverse-memory-meets-memory-ratios: that forces a nontrivial decoder element into M M^-1; this forces one into M^-1 unless both memories carry positive relations, and it adds the permutive normal form in that case.
  forward-relations-of-a-counterexample-have-a-nonsofic-core: that peels the forward relator hypergraph to a nonsofic two-core; this reads positivity of the memories themselves, so it excludes whole memory pairs inside any subsemigroup avoiding 1, whatever relations they satisfy.
  amenable-decoder-memory-forces-surjectivity: that excludes decoder memories generating amenable groups; this excludes memory pairs lying in a subsemigroup that avoids 1, which covers nonamenable groups such as free groups and positive cones of left orders.
---

**ESTABLISHED** by `strict-pairs-inverted-memory-or-positive-relations-proof`.

Let `G` be a group and `A` a finite alphabet. Let `tau` be a cellular automaton with memory
`M` (containing `1`) and rule `mu`, and `sigma` one with memory `S` (containing `1`) and rule
`nu`, such that `sigma tau = id`.

**Theorem.** If `tau` is not surjective, then at least one of the following holds.
1. `s m = 1` for some `s` in `S` with `s != 1` and some `m` in `M`.
2. There is a nonempty `E` inside `M \ {1}` with `E ⊆ (S \ {1}) (E ∪ {1})` such that
   - some product `e_1 ... e_k` of elements of `E` equals `1`, and
   - some product `s_1 ... s_j` of elements of `S \ {1}` equals `1`;
   and `tau(x)(g) = f_(x restricted to gE)(x(g))` for a family of permutations `f_c` of `A`.

**Corollary (memory positivity filter).** Suppose `M \ {1}` and `S \ {1}` lie in one
subsemigroup `P` of `G` with `1 ∉ P`. Then no strict pair uses these memories, for any alphabet
and any rules. In case 1, `s m = 1` with `s, m` in `P` puts `1` in `P`; in case 2 a product of
elements of `E ⊆ P` is `1`.

Examples of such `P`: the positive cone of a left-invariant order; the elements with positive
value under a homomorphism `G -> R`; a free subsemigroup avoiding `1`.

**Scope.** Case 2 keeps every design that is permutive in the identity symbol and whose memories
carry relations, which includes linear pairs with torsion or with both `s` and `s^-1` in a memory.
So this is a filter, not a proof of any open root. No priority is claimed.
