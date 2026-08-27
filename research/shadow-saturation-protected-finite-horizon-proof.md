---
rg: 2
id: shadow-saturation-protected-finite-horizon-proof
kind: route
title: Increase Hull's injectivity ball while keeping the same shadow reservoir
target: shadow-saturation-protected-finite-horizon
requires:
  - single-shadow-word-saturation-compiler
  - common-quotient-onto-normal-subgroup
artifacts:
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
---

For each radius, include a sufficiently large finite source ball and the bug
word in Hull's protected set.  The router still chooses both reservoir
generators in `<<w>>` and still forces its image to be the whole quotient.
The protected set survives, while shadow functoriality and the Kazhdan
detector give full MF radical.  Letting the protected radii tend to infinity
is exactly convergence of the induced markings to the source marking.
