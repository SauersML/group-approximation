---
rg: 2
id: stw99-lxxvi-cu-regular-inductive-limit-proof
kind: route
title: Apply continuity of Cu to the natural tensor-stabilization diagram
target: stw99-lxxvi-cu-regularity-passes-to-inductive-limits
requires: []
---

Since `Z` is nuclear, hence exact, minimal tensoring by `Z` commutes with
C\*-inductive limits, including systems with noninjective connecting maps:

```text
A tensor_min Z = lim_n (A_n tensor_min Z).
```

The Cuntz semigroup functor is continuous for C\*-inductive limits.  Hence

```text
Cu(A) = lim_n Cu(A_n),
Cu(A tensor_min Z) = lim_n Cu(A_n tensor_min Z).
```

Naturality of the first-factor maps gives a morphism between these two
inductive systems whose component at every `n` is an isomorphism.  Its
induced map on the colimits is therefore an isomorphism, and this induced map
is exactly `Cu(iota_A)`.
