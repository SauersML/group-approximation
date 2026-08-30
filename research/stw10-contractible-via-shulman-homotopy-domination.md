---
rg: 2
id: stw10-contractible-via-shulman-homotopy-domination
kind: route
title: Dominate a contractible algebra by the zero algebra
target: stw10-contractible-algebras-have-qd-amenable-traces
requires:
  - stw10-homotopy-domination-preserves-amenable-qd
---

Let `A` be separable and contractible and put `B=0`. For the unique star
homomorphisms `f:A -> B` and `g:B -> A`, the composite `g f` is the zero
homomorphism. Contractibility says precisely that this map is homotopic to
`id_A`; hence `A` is homotopically dominated by `B`.

The zero algebra is exact. It has no tracial states, so every amenable trace
on it is quasidiagonal vacuously; under a convention admitting the zero
trace, that trace is quasidiagonal directly. Apply the required
homotopy-domination theorem.
