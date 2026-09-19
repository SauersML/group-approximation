---
rg: 2
id: stable-classifiable-z-crossed-proof
kind: route
title: Tensor the Elliott-Sato-Thomsen presentation of the stabilized Jiang-Su algebra
target: stable-classifiable-algebras-are-z-crossed-products
requires: []
---

Elliott--Sato--Thomsen (CMP; STW quote it at Problem XLVI's
discussion) present `Z ⊗ K ≅ B ⋊_α Z` for a classifiable algebra `B`.
For stable classifiable `A`:

```text
A ≅ A ⊗ Z ⊗ K ≅ A ⊗ (B ⋊_α Z) ≅ (A ⊗ B) ⋊_{id ⊗ α} Z ,
```

using `Z`-stability and stability of `A` in the first step and
commutation of crossed products with a trivially-acted tensor factor
in the last.  `C := A ⊗ B` is simple (both factors simple, one
nuclear), separable, nuclear, `Z`-stable (first factor), and satisfies
the UCT (both factors are in the bootstrap class, which is closed
under minimal tensor products) — i.e. classifiable.
