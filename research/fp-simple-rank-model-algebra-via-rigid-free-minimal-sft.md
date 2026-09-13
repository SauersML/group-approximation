---
rg: 2
id: fp-simple-rank-model-algebra-via-rigid-free-minimal-sft
kind: route
title: A quantum rigid free minimal SFT has a finitely presented simple crossed product with a Følner rank model
target: fp-simple-algebra-over-finite-field-with-rank-model
requires: [free-minimal-z2-sft-is-quantum-rigid, sft-crossed-product-fp-iff-quantum-rigid, free-minimal-crossed-products-are-simple-with-rank-models]
---

Let `Ω` be a free minimal `Z^2`-SFT that is `D`-quantum rigid, and let `k` be a finite field.

- **Finite presentation.** By the second claim, `R = LC(Ω, k) ⋊ Z^2` is finitely presented as a
  `k`-algebra. Take `D >= r`, which rigidity allows.
- **Simplicity and the rank model.** By the third claim, `R` is simple with an injective unital rank
  model.
- **Infinite-dimensional.** `Ω` is infinite.
