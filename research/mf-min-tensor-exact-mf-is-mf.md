---
rg: 2
id: mf-min-tensor-exact-mf-is-mf
kind: claim
title: The spatial tensor product of an MF algebra with a separable exact MF algebra is MF
distinct_from:
  hyperfinite-factor-not-quasidiagonal: that is Ozawa's MF algebra whose spatial tensor product with the non-exact factor R is infinite; this shows infiniteness cannot occur when the second factor is exact and MF, which is why that example needs a non-exact factor.
artifacts:
  - research/artifacts/uct-fresh-mf-tensor-route-2026-09-12.md
---

**ESTABLISHED (derivation `mf-min-tensor-exact-mf-proof`).** Let `A` be a
separable MF C\*-algebra and `C` a separable exact MF C\*-algebra. Then
`A ⊗_min C` is MF, hence stably finite.

Contrapositive, the form this graph uses: if `A` is separable MF, `C` is
separable exact, and `A ⊗_min C` is not stably finite, then `C` is not MF. In
particular `C` has no faithful quasidiagonal trace.

Credit: this is standard permanence for MF algebras and is very likely
already in the literature (Blackadar--Kirchberg). No novelty is claimed, and
the literature was not searched for a printed statement.
