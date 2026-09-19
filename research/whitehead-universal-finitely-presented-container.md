---
rg: 2
id: whitehead-universal-finitely-presented-container
kind: claim
title: One two-generator finitely presented group Whitehead-injectively contains every recursively presented group
distinct_from:
  whitehead-universal-finitely-presented-torsion-free-group: that constructs a torsion-free host for the torsion-free input class and packages the Whitehead conjecture; this host allows torsion and contains every countably generated recursively presented group.
  whitehead-injective-torsion-order-preserving-higman-embedding: that chooses a separate finitely presented host after each finitely generated recursive input; this chooses one host before every input.
  whitehead-vanishing-universal-test-group: that asks for vanishing in an uncountable restricted product of torsion-free groups; this is a countable universal container and its Whitehead group is necessarily nonzero.
  mikaelian-explicit-higman-embedding: that supplies a finitely presented host for one recursive presentation without Whitehead control; this is simultaneous and Whitehead-injective.
---

There exists one two-generator finitely presented group `U` such that every countably
generated recursively presented group `K` admits an embedding

```text
i_K: K -> U
```

for which

```text
Wh(i_K): Wh(K) -> Wh(U)
```

is injective. The quantifier order is `exists U, for every K, exists i_K`:
the group `U` is fixed independently of `K`.

Moreover

```text
Tord(U) = {2,3,4,...}.
```

Indeed `U` contains every finite group. This is a universal Whitehead
container, not a vanishing tester: it contains `C_5` Whitehead-injectively,
so `Wh(U)` is nonzero.

**ESTABLISHED 2026-08-30** by
[[whitehead-universal-container-via-enumeration-and-rope]].
