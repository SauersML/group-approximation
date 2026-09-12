---
rg: 2
id: stw95-af-factor-preserves-purity-proof
kind: route
title: Transport Cu(Z)-absorption through the AF external-product isomorphism
target: stw95-af-factor-preserves-purity
requires:
  - stw95-af-factor-external-cu-map-isomorphism
---

Put `R=Cu(𝒵)`.  Since `B` is pure, Antoine--Perera--Thiel's
characterization gives `Cu(B) tensor_Cu R ≅ Cu(B)`.  Associativity and
symmetry yield

```text
(Cu(C) tensor_Cu Cu(B)) tensor_Cu R
  ≅ Cu(C) tensor_Cu (Cu(B) tensor_Cu R)
  ≅ Cu(C) tensor_Cu Cu(B).
```

Thus the abstract tensor product is both almost unperforated and almost
divisible.  The AF external-product isomorphism identifies it with
`Cu(C tensor_min B)`, proving purity.
