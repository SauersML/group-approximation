---
rg: 2
id: amenable-basis-coinduction-cannot-create-envelope
kind: claim
title: Coinduction of an amenable group basis cannot create the rigid envelope
distinct_from:
  coinduction-retains-crossed-product-not-relation: that identifies the distinguished coordinate for a commutative pmp source; this applies the same faithful-coordinate mechanism to group factors and combines it with the Haagerup rigidity fence.
  coinduction-preserves-but-cannot-create-algebraic-envelope: that treats compact-abelian Haar bases and infinite-index coset corners; this treats noncommutative amenable group bases and does not use Pontryagin duality.
---

Let `Gamma<Lambda`, with `Gamma` Haagerup, let `K_0` be countable amenable,
and let `Gamma -> Aut(K_0)`.  Form the group-basis coinduction

```text
K = direct_sum_(Lambda/Gamma) K_0
```

with the cocycle-twisted coordinate action of `Lambda`.  Inside
`L(K) rtimes Lambda`, the distinguished coordinate together with the
`Gamma`-unitaries generates a faithful copy of

```text
L(K_0) rtimes Gamma,                                  (AGC1)
```

not a stabilizer-forgetting relation quotient.  The algebra `(AGC1)` cannot
contain the fixed property-`(T)` relation factor.  Therefore ordinary
coinduction from the native virtually-free actor to `SL_3(Z)` (or to a group
containing it) does not create `amenable-group-basis-sl3-envelope`; any
successful ambient inclusion would have to use the new coordinates and the
larger actor in an essentially non-coordinate way.

