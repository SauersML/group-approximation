---
rg: 2
id: thompson-v-f2-linear-sofic-from-soficity
kind: route
title: A sofic Thompson V is F_2-linear sofic
target: thompson-v-is-f2-linear-sofic
requires:
  - thompson-v-is-sofic
  - sofic-implies-linear-sofic-over-every-field
---

If `V` is sofic, then `sofic-implies-linear-sofic-over-every-field` with `F = F_2` gives an injective
homomorphism of `V` into a characteristic-two matrix rank ultraproduct. That is
`thompson-v-is-f2-linear-sofic`.

*Checked by `gk-vf-linear` (2026-09-12), Section 51 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: valid.*
