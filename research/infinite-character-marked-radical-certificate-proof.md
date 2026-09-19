---
rg: 2
id: infinite-character-marked-radical-certificate-proof
kind: route
title: Multiply the seed expansion estimate by the central-sign mass identity
target: infinite-character-interface-is-marked-radical-certificate
requires:
  - one-seed-infinite-character-expansion-collapses-mark
  - hyperlinear-radical-presentation-compactness
  - central-d8-seed-preserves-hyperlinearity
---

Formula `(ISC3)` says

```text
mu<=2E_act/gamma+eta_seed^2/4.
```

Since `J` is an exact involution and `P=(1-J)/2`, normalized trace gives
`||J-I||_2^2=4mu`, proving `(ICR1)` and `(ICR2)`.
`hyperlinear-radical-presentation-compactness` turns the presentation
modulus into radical membership.  The finite-edge equivalence
`central-d8-seed-preserves-hyperlinearity` then transfers nonhyperlinearity
to the base semidirect product.

For canonical microstates of a surviving mark, `mu->1/2` and the seed
defect tends to zero.  Rearranging `(ISC3)` gives `(ICR3)`.

