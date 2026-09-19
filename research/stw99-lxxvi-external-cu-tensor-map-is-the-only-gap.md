---
rg: 2
id: stw99-lxxvi-external-cu-tensor-map-is-the-only-gap
kind: claim
title: For a pure algebra, Cu-regularity is exactly invertibility of the external Cu tensor map
distinct_from:
  stw99-problem-lxxvi-pure-implies-cu-regular: that asks whether the external map is always invertible; this is the unconditional factorization reducing the problem to that map.
---

Let `A` be a pure C\*-algebra, put `S=Cu(A)`, and let `z=[1_Z]`.  Let

```text
eta_A : S -> S tensor_Cu Cu(Z),       x |-> x tensor z
```

and let

```text
mu_A : S tensor_Cu Cu(Z) -> Cu(A tensor_min Z)
```

be induced by the external Cuntz product `([a],[b]) |-> [a tensor b]`.
Then `eta_A` is an isomorphism and

```text
Cu(iota_A)=mu_A o eta_A.
```

Consequently, `A` is Cuntz semigroup regular if and only if `mu_A` is an
isomorphism.
