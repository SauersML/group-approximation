---
rg: 2
id: fpbs-dead-product-peres-all-gens
kind: route
title: Dead - apply Peres's product theorem to every generating set
target: fpbs-product-every-generating-set
requires: []
---

**Dead.** This route would deduce `fpbs-product-every-generating-set` directly
from the product-generating-set results (Grimmett--Newman, the nonunimodular
route, Peres 2000) by treating an arbitrary Cayley graph of `H x K` as a
Cartesian product of the two factors. It is invalidated by
`fpbs-mixed-gen-set-not-cartesian`: a generating set containing an element that
moves both coordinates gives edges belonging to no single factor, so the
Cartesian-product proof structure those theorems rely on is unavailable. A
genuine generating-set-transfer argument is required instead; recorded in the
`## Attempts` of the target.
