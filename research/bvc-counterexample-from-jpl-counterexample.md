---
rg: 2
id: bvc-counterexample-from-jpl-counterexample
kind: route
title: A counterexample to the Juan-Pineda–Leary conjecture is a counterexample to the von Puttkamer–Wu conjecture
target: some-fp-non-vc-group-has-property-bvc
requires:
  - some-non-vc-group-has-a-finite-evc-model
  - finite-evc-model-implies-fp-and-bvc
---

A group `G`, not virtually cyclic, with a finite model for `E_VC G`, is finitely presented
and has BVC by `finite-evc-model-implies-fp-and-bvc`. So it witnesses
`some-fp-non-vc-group-has-property-bvc`.
