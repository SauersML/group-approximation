---
rg: 2
id: whitehead-universal-finitely-presented-torsion-free-group
kind: claim
title: One finitely presented torsion-free group tests the global Whitehead conjecture
distinct_from:
  whitehead-vanishing-universal-test-group: that asserts vanishing for an explicit uncountable restricted product; this proves the existence of a finitely presented tester but does not assert that its Whitehead group vanishes.
  whitehead-vanishing-finitely-presented-torsion-free: that is the still-open vanishing statement; this is the established universal embedding and equivalence package reducing it to one group.
  whitehead-injective-torsion-free-embedding: that builds a host separately for each finitely generated recursively presented group; this constructs one host working Whitehead-injectively for the entire countably generated recursively presented torsion-free class at once.
---

There exists a finitely presented torsion-free group U such that every
countably generated recursively presented torsion-free group K admits an
embedding

    K -> U

whose induced map Wh(K)->Wh(U) is injective.

Consequently the following are equivalent:

1. Wh(U)=0.
2. Wh(K)=0 for every countably generated recursively presented torsion-free
   group K.
3. Wh(K)=0 for every finitely generated recursively presented torsion-free
   group K.
4. Wh(G)=0 for every finitely presented torsion-free group G.
5. Wh(G)=0 for every torsion-free group G.

The universal embeddings give 1=>2, restriction gives 2=>3=>4, and the
finite-support recursively-presented reduction already in Cairn gives
3=>5. Finally 5=>1 because U is torsion-free.

**ESTABLISHED 2026-08-30** by
[[whitehead-universal-group-via-effective-hnn-and-rope]]. This is a strict
upgrade of the old uncountable test-group packaging: the remaining
Whitehead conjecture is one computation on a single finitely presented
torsion-free group.
