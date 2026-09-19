---
rg: 2
id: steinberg-x-dual-via-ordinary-additive-fourier-blocks
kind: route
title: Prove X-dual surjectivity one additive b-frequency at a time
target: steinberg-x-plus-incidence-dual-is-surjective
requires:
  - steinberg-zero-marginal-space-is-biaffine-circulation
---

Diagonalize translation in the `b` coordinate by nontrivial additive
characters, identify the endpoint-potential subspace in each frequency, and
try to prove that `X_ch^*` spans the complementary frequency block.

This route is invalidated by
`steinberg-ordinary-fourier-blocks-do-not-descend-mod-p`: the required
characters do not split the defining-characteristic translation module,
and the `A^(-1),B^(-1)` terms do not preserve the proposed frequency blocks
even over an auxiliary splitting field.
