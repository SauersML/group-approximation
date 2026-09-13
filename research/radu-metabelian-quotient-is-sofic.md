---
rg: 2
id: radu-metabelian-quotient-is-sofic
kind: claim
title: The metabelian quotient Gamma_R/[Lambda_v, Lambda_v] of Radu's BMW lattice is sofic
distinct_from:
  radu-metabelian-quotient-is-not-sofic: this is its negation
  radu-nilpotent-by-arithmetic-quotients-are-sofic: that asks for soficity of every Gamma_R/gamma_k(Lambda_v); this is the case k = 2, which is necessary for that claim and not sufficient
---

**OPEN.** `G_2 = Γ_R/[Λ_v, Λ_v]` is sofic. This is the case `k = 2` of
`radu-nilpotent-by-arithmetic-quotients-are-sofic`. It is necessary for that claim, and it does not
imply soficity of `Γ_R`.

`G_2` embeds in `Z^2 wr_(Q/C_χ) Q` (`radu-metabelian-quotient-embeds-in-edge-lamp-wreath`). So the
claim follows from soficity of the one coset action `Q ↷ Q/C_χ`
(`radu-metabelian-quotient-sofic-via-edge-coset-action`). Genuine finite models of that action are
excluded (`radu-square-lamp-forces-reflections-in-finite-actions`).
