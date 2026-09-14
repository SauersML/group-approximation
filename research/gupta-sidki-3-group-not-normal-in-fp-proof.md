---
rg: 2
id: gupta-sidki-3-group-not-normal-in-fp-proof
kind: route
title: The Gupta–Sidki 3-group is not normal in a finitely presented group because its Out is locally finite
target: gupta-sidki-3-group-is-a-normal-subgroup-of-no-fp-group
requires:
  - centerless-normal-subgroups-with-locally-finite-out-of-fp-are-fp
  - gupta-sidki-3-group-centerless-not-fp-with-lf-out
---

Suppose `G` is finitely presented and `N ⊴ G` with `N ≅ 𝔊𝔖`. By
`gupta-sidki-3-group-centerless-not-fp-with-lf-out`, `N` has trivial center and
locally finite `Out`. So `N` is finitely presented
(`centerless-normal-subgroups-with-locally-finite-out-of-fp-are-fp`), contradicting item 3 of the
import.
