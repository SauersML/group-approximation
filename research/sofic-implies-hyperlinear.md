---
rg: 2
id: sofic-implies-hyperlinear
kind: claim
title: Soficity implies hyperlinearity
---

`Sofic/Hyperlinear.isHyperlinear_of_isSofic` (formalized), with
`IsHyperlinear` defined by unitary matrices in the normalized
Hilbert–Schmidt metric. Proof: the metric identity
`‖P_σ − P_τ‖²_{HS,norm} = 2·d_H(σ,τ)` plus the fact that `σ ↦ P_{σ⁻¹}` is a
genuine homomorphism (the inverse matters — `permMatrix` itself is an
anti-homomorphism). The converse is hyperlinear-nonsofic-group.
