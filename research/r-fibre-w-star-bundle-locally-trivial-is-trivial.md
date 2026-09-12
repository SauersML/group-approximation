---
rg: 2
id: r-fibre-w-star-bundle-locally-trivial-is-trivial
kind: claim
title: A locally trivial W*-bundle whose fibres are all the hyperfinite II_1 factor is trivial
distinct_from:
  stw22-locally-trivial-finite-dimensional-bundles: that proves trace continuity for locally trivial hyperfinite bundles over finite-dimensional bases by a chartwise colouring; this is the global triviality theorem of Evington--Pennig over an arbitrary compact Hausdorff base.
artifacts:
  - research/artifacts/tw-bundle-hunter-bundle-localization-2026-09-12.md
---

Let `M` be a W*-bundle over a compact Hausdorff space `X` with every fibre
isomorphic to the hyperfinite II_1 factor `R`.  Suppose `M` is locally trivial:
every `x ∈ X` has a closed neighbourhood `Y` with `M_Y ≅ C_σ(Y,R)`.  Then
`M ≅ C_σ(X,R)`.

There is no covering-dimension hypothesis.  The proof uses Popa--Takesaki
contractibility of `Aut(R)`.  So no gluing of trivial pieces along
`Aut(R)`-valued transition data produces a nontrivial `R`-fibre bundle: a
nontrivial one must fail local triviality at some point.
