---
rg: 2
id: f-infinity-amenable-non-ea-via-grigorchuk-hnn
kind: route
title: If Grigorchuk's finitely presented amenable HNN extension is FP_infinity, it answers Zaremsky 1.12
target: there-is-f-infinity-amenable-non-elementary-amenable-group
requires:
  - grigorchuk-hnn-extension-is-fp-amenable-non-ea
  - grigorchuk-hnn-extension-is-fp-infinity
---

1. `𝔊^` is finitely presented, amenable and not elementary amenable
   (`grigorchuk-hnn-extension-is-fp-amenable-non-ea`).
2. If `𝔊^` is of type `FP_∞` (`grigorchuk-hnn-extension-is-fp-infinity`), then
   it is of type `F_∞`: a finitely presented group of type `FP_∞` over `Z` is
   of type `F_∞`. Take a finite presentation complex, and then kill the finitely
   generated `π_n = H_n` of the universal cover of the `n`-skeleton at each stage.
3. So `𝔊^` is an amenable, non-elementary amenable group of type `F_∞`.

The second premise is open, so this route does not establish its target.
