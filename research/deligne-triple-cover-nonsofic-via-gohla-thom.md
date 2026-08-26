---
rg: 2
id: deligne-triple-cover-nonsofic-via-gohla-thom
kind: route
title: Gohla--Thom Theorem 3.13 at the symplectic lattice with Z/3 coefficients
target: deligne-triple-cover-is-not-sofic
requires:
  - gohla-thom-stable-base-nonsofic-extension
  - sp4-z-satisfies-gohla-thom-hypotheses
---

Instantiate Theorem 3.13 of Gohla--Thom with `Gamma = Sp_4(Z)` (residually
finite and finitely presented, hence of finite type), `A = Z/3`, and
`Gamma~ = E_3`, Deligne's non-residually-finite triple cover (hypothesis
(iii)).  Hypothesis (ii) and stability in finite actions are
`sp4-z-satisfies-gohla-thom-hypotheses`.  The conclusion is that `E_3` is
not sofic.
