---
rg: 2
id: thompson-v-carmichael-compiler-linear-collapse-proof
kind: route
title: Use compact packing in one direction and the constant Carmichael packet in the other
target: thompson-v-carmichael-compiler-is-linear-mark-collapse
requires:
  - thompson-carmichael-collapse
---

For the forward implication, apply `thompson-carmichael-collapse` to the
conjugates supplied for arbitrarily large `M`.  Its two-matrix estimate and
compact packing give

```text
||U(b)-I||_2<=2C def_R(U).
```

For the converse, assume `||U(b)-I||_2<=K def_R(U)` and take every conjugator
to be the identity.  All packet entries are then the same matrix `B=U(b)`.
The cube relation costs at most the presentation defect, and

```text
(B B)^2-I=B^4-I=B(B^3-I)+(B-I).
```

Hence every pair relation costs at most `(K+1)def_R(U)`, independently of
the number of entries and the matrix dimension.  This is precisely the
uniform Carmichael-family conclusion.

