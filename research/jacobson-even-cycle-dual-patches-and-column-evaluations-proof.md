---
rg: 2
id: jacobson-even-cycle-dual-patches-and-column-evaluations-proof
kind: route
title: Close both cyclic boundaries by contragredient actions and inspect increasing natural-module columns
target: jacobson-literal-column-normalizer-is-lef
requires:
  - jacobson-whole-column-normalizer-has-marked-lef-models
  - jacobson-coherent-group-is-an-ascending-corner-extension
artifacts:
  - research/artifacts/jacobson-literal-column-normalizer-is-lef-2026-09-08.md
---

On a cycle of length `2n`, use the reflections `w(k)=-k-1`,
`h(k)=-k` and the shear from the negative half to its reflected positive
half. The opposite local chart exchanges the two constant shears and
fixes the reflections: it carries the inverse-transpose of the original
representation. A fixed actor word has bounded radial propagation, so
each starting vector is tested entirely within one valid chart. This
proves eventual exactness of every literal actor identity. The original
chart detects nonidentities.

Evaluate both Jacobson coefficients on the first `floor(n/4)` input
columns of the unilateral module. Their bounded propagation proves
eventual exact covariance, and faithful column evaluation retains every
nonzero additive element. Finite affine groups therefore give injective
local multiplication models of the actual semidirect product.

Conjugates of the marked actor commutator generate all finitary roots,
including both cross-parity directions. The resulting infinite simple
finitary group is killed in every exact finite-dimensional unitary
representation, and its commutators with the column generate `I^2`.
The remaining affine Laurent quotient is residually finite, proving the
exact residual calculation. The cover's finite generation descends,
and finite presentation together with LEF would imply residual finiteness.
