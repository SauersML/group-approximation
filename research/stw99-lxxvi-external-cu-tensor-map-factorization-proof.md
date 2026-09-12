---
rg: 2
id: stw99-lxxvi-external-cu-tensor-map-factorization-proof
kind: route
title: Factor the first-factor Cu map through the abstract Cu tensor product
target: stw99-lxxvi-external-cu-tensor-map-is-the-only-gap
requires: []
---

The map

```text
Cu(A) times Cu(Z) -> Cu(A tensor_min Z),
([a],[b]) |-> [a tensor b],
```

is a Cu-bimorphism, so the universal property of `tensor_Cu` gives `mu_A`.
For every `x=[a] in Cu(A)`,

```text
(mu_A o eta_A)(x)
 = mu_A([a] tensor [1_Z])
 = [a tensor 1_Z]
 = Cu(iota_A)(x).
```

The imported abstract characterization of pureness says precisely that
`eta_A` is an isomorphism when `A` is pure.  Composing with an isomorphism
shows that `Cu(iota_A)` is an isomorphism exactly when `mu_A` is.  No
identification of `Cu(A) tensor_Cu Cu(Z)` with `Cu(A tensor_min Z)` is used.
