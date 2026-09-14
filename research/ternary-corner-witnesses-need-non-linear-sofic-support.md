---
rg: 2
id: ternary-corner-witnesses-need-non-linear-sofic-support
kind: claim
title: Any solution of the ternary anti-central corner equation is supported on a subgroup that is not linear sofic over F_3
distinct_from:
  determinant-violation-needs-nonsofic-support-subgroup: that is the support constraint for a violation of the determinant conjecture; this is the support constraint for the ternary corner equation, through direct finiteness of the subgroup algebra.
  ternary-anti-invariant-swap-corner-is-full: that is the open corner equation itself; this is an established filter on where its witnesses can live.
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

Let `b, c` in `S_- = eps_- F_3[G_3]` satisfy `c e_- b = eps_-`, and let
`H = <z, w, supp b, supp c> <= G_3`.
- `H` is not `F_3`-linear sofic.
- Hence `H` is not sofic, and in particular not amenable and not residually finite.

Use: a search or construction may discard any candidate pair whose support, together with `z` and `w`,
generates a sofic subgroup.

Proof: Theorem C of the artifact.
