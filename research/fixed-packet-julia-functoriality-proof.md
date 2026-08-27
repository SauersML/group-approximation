---
rg: 2
id: fixed-packet-julia-functoriality-proof
kind: route
title: Replace the packet multiplicity matrices by a finite von Neumann algebra
target: fixed-packet-julia-calculus-is-tracially-functorial
requires:
  - julia-dilation-packages-heat-as-one-cross-gram-moment
  - packet-natural-selectors-cannot-extract-one-bounded-copy
  - universal-block-return-violates-the-regular-firewall
---

Schur decomposition identifies the selected finite type with
`M_r(C) tensor 1` and its commutant with the multiplicity algebra.  Every
listed block operation is a C-star-algebra operation and therefore remains
defined after replacing `M_m(C)` by an arbitrary finite tracial algebra
`N`.  Continuous functional calculus commutes with unital star
homomorphisms, so the Julia defect square roots introduce no matrix-specific
step.

If `(FJC3)` followed from these operations, apply it in the selected corner
of the regular tracial representation and use
`tau(YX)=tau(XY)`.  Formula `(JHG3)` makes the right side tend to zero with
`t`, while faithfulness keeps the nonzero projection `P` at positive trace,
a contradiction.  Hence some operation outside the fixed-packet Julia
calculus is necessary.
