---
rg: 2
id: finite-commuting-extension-of-a-sofic-action-is-sofic-proof
kind: route
title: Tensor the model with the regular Phi-set and twist each chart by the Phi-coordinate
target: finite-commuting-extension-of-a-sofic-action-is-sofic
requires: []
artifacts:
  - research/artifacts/twisted-rope-rf-envelope-2026-09-13-part2.md
---

Let `F' <= G x Phi` be finite, `E <= X` finite, and `eps > 0`. Let `F` be the
projection of `F'` to `G`, and put `E' = Phi.E`. Take a unital
`(F,eps)`-multiplicative `phi : G -> Sym(A)` that is an `(F,E',eps)`-orbit
approximation, with set `B`, good set `S` and injective charts
`pi_a : E' -> B`.

**The model.** On `A x Phi` put `phi'(g,psi) = phi(g) x L_psi`, with good
set `S x Phi`, the same `B`, and charts
`pi'_(a,chi)(x) = pi_a(chi^-1 x)` for `x in E`. `phi'` is unital and
`(F',eps)`-multiplicative, since the second factor is an exact action. Each
chart is injective, because `chi^-1 E <= E'`.

**The chart identity.** Suppose `(g,psi) in F'`,
`(phi(g)a, psi chi) in S x Phi`, and `(g,psi)^-1 x in E`. Put
`y = chi^-1 psi^-1 x`. Then `y in E'`, and
`g^-1 y = chi^-1 ((g,psi)^-1 x) in E'`. The identity for `phi` gives
`pi_(phi(g)a)(y) = pi_a(g^-1 y)`, which reads
`pi'_(phi(g)a, psi chi)(x) = pi'_(a,chi)((g,psi)^-1 x)`, because the actions
of `G` and `Phi` on `X` commute. This is GKP Definition 2.1(3) for `phi'`.
