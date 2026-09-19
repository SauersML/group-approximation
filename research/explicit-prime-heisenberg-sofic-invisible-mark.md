---
rg: 2
id: explicit-prime-heisenberg-sofic-invisible-mark
kind: claim
title: Every prime occurs as a hyperfinite-invisible mark in a finitely generated sofic group
distinct_from:
  literal-group-mark-invisible-to-hyperfinite-representations: that treats the order-two mark in the manuscript's finitely presented Clifford-lamp group; this gives a simpler finite-amalgam construction for every prime order, but does not claim finite presentability.
  deligne-triple-cover-fd-central-invisibility: that kills an order-three centre only in finite-dimensional representations using arithmetic character rigidity; this kills its prime-order mark in every finite injective representation using a Heisenberg phase and a Bernoulli compressor.
  prime-heisenberg-compressor-hyperfinite-invisibility: that is an abstract criterion; this constructs a finitely generated sofic group satisfying every hypothesis and proves the marked element remains nontrivial.
artifacts:
  - research/artifacts/prime-heisenberg-sofic-invisibility-2026-08-30.md
---

For every prime `p` there is a finitely generated sofic group `Gamma_p`
with a nontrivial central element `w_p` of order `p` such that every
homomorphism

```text
rho:Gamma_p -> U(W)
```

into a finite injective von Neumann algebra satisfies `rho(w_p)=1`.
Consequently

```text
Gamma_p embeds in U(R^omega), but Gamma_p does not embed in U(R).        (EPH1)
```

The construction uses no property `(T)`, residual-finiteness conclusion, or
classification of characters.  The group is a finite amalgam of an explicit
LEF affine-shift group with the order-`p` Heisenberg group.  A finitary
elementary linear group makes every nonzero Bernoulli lamp conjugate to one
Heisenberg generator, while a free subgroup supplies the nonamenable
properly outer action.
