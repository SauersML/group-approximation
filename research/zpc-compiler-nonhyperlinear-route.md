---
rg: 2
id: zpc-compiler-nonhyperlinear-route
kind: route
title: A selector-sound LCS compiler turns the perfect ZPC-IRS gap into a nonhyperlinear group
target: non-hyperlinear-group
requires:
  - perfect-zpc-irs-quantum-gap-game
  - controlled-linear-predication-normal-form
  - zpc-selector-sound-lcs-compiler
  - perfect-lcs-gap-implies-nonhyperlinear
artifacts:
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
---

Apply `zpc-selector-sound-lcs-compiler` to the finite tailored game `G` from
`perfect-zpc-irs-quantum-gap-game`. Perfect ZPC-IRS completeness gives a
perfect commuting strategy for `L(G)`. If `L(G)` had a perfect
finite-dimensional strategy, sound decoding would produce a perfect
finite-dimensional strategy for `G`, contradicting `omega*(G)<1/2`. Hence
`L(G)` has commuting value one and finite-dimensional quantum value below one.
`perfect-lcs-gap-implies-nonhyperlinear` then gives a nonhyperlinear solution
group.

The predication claim records that controlled linear equations themselves are
no longer the unknown part of the compiler; selector soundness is.
