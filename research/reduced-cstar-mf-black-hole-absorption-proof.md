---
rg: 2
id: reduced-cstar-mf-black-hole-absorption-proof
kind: route
title: Restrict an MF-target map to the common unit
target: reduced-cstar-mf-black-hole-absorption
requires:
  - hilbert-hotel-cstar-total-invisibility
artifacts:
  - research/reduced-cstar-mf-black-hole-absorption.md
---

Let `i : B -> A` be an injective unital star homomorphism, with `B` an MF
black hole, and let `phi : A -> M` be a star homomorphism to an MF algebra.
The composite `phi o i` is zero.  Since `i` is unital,

```text
phi(1_A) = phi(i(1_B)) = 0.
```

A star homomorphism from a unital C-star algebra which kills the unit is
zero.  Thus `A` is an MF black hole.

For a subgroup `H <= G`, the canonical map `C*_r(H) -> C*_r(G)` is an
injective unital star homomorphism: decompose `l^2(G)` into right-coset copies
of `l^2(H)` and restrict the left regular representation.  Hence the result
applies to every supergroup.

Every standard unital tensor-product completion contains the first factor
unitally through `b |-> b tensor 1`; the same restriction argument applies
to crossed products and amalgams whenever their structural map is injective
and unital.  A quotient map onto a nonzero quotient is unital, so no nonzero
quotient of an MF black hole can be MF.

