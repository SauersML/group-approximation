---
rg: 2
id: thompson-v-carmichael-compiler-is-linear-mark-collapse
kind: claim
title: The uniform Thompson Carmichael compiler is exactly linear collapse of its marked three-cycle
distinct_from:
  thompson-v-r5-coherent-carmichael-family: that is phrased as an unbounded family of conjugates with uniformly controlled Carmichael relators; this proves that the family exists if and only if the marked generator already satisfies the linear collapse estimate the family was meant to establish.
  thompson-carmichael-collapse: that proves only the family-to-collapse direction by compact packing; this supplies the reverse direction by one constant packet and identifies the exact logical strength of the open compiler.
  carmichael-energy-uniform-criteria-incomparable: that compares the uniform and subquadratic aggregate packet hypotheses at a fixed positive scale; this compares the uniform R5 compiler with a presentation-level linear estimate on the marked word.
---

Fix the Bleak--Quick presentation and put

```text
B=U(b),                 b=(01 10 11),
delta=def_R(U).
```

The following two dimension-independent assertions are equivalent, with
constants changing only by an absolute additive factor.

1. There are `C,delta_0>0` such that every tuple with
   `delta<=delta_0` and every `M>=2` admit unitary conjugates

   ```text
   X_i=W_i B W_i^*,
   ||X_i^3-I||_2<=C delta,
   ||(X_iX_j)^2-I||_2<=C delta       (i!=j).             (TLC1)
   ```

2. There are `K,delta_0>0` such that every such tuple satisfies

   ```text
   ||B-I||_2<=K delta.                                  (TLC2)
   ```

Indeed `(TLC1) => (TLC2)` is exactly
`thompson-carmichael-collapse`, which gives `K=2C`.  Conversely, assume
`(TLC2)` and choose the constant packet

```text
W_i=I,                  X_i=B                         (1<=i<=M).
```

The cube condition is one of the fixed presentation relators, so
`||B^3-I||_2<=delta` after incorporating its fixed word-evaluation constant
in the definition of `delta`.  Moreover

```text
B^4-I = B(B^3-I)+(B-I),                                (TLC3)
```

and unitary invariance plus the triangle inequality give

```text
||(X_iX_j)^2-I||_2=||B^4-I||_2<=(K+1)delta.            (TLC4)
```

Thus `(TLC1)` holds for every `M` with `C=max(1,K+1)`.

Consequently the open uniform Carmichael-family compiler is not an
intermediate local-to-global synchronization theorem weaker than marked-word
collapse.  Constructing its unbounded family with a uniform R1--R5 defect
budget already proves the desired linear estimate, while that estimate makes
the family tautological.  The exact prefix-code copies of finite symmetric
groups remain useful motivation, but no proof effort is saved merely by
rephrasing `(TLC2)` as the search for the conjugators `W_i`.

