---
rg: 2
id: gl-n-q-via-projective-elementary-hosts
kind: route
title: A ring containing Q with finitely presented simple PE_N(R) for infinitely many N hosts every GL_n(Q)
target: gl-n-q-embeds-in-fp-simple-group
requires:
  - q-algebra-elementary-quotients-contain-gl-n-q
  - q-algebra-with-fp-simple-projective-elementary-group
artifacts:
  - research/artifacts/gq-gq-en-ring-elementary-route.md
---

Let `R ⊇ Q` be as in `q-algebra-with-fp-simple-projective-elementary-group`, and
let `n >= 2`.
1. Choose one of the infinitely many ranks with `N >= n+2`.
2. By `q-algebra-elementary-quotients-contain-gl-n-q` (part 4),
   `g ↦ [diag(g, det(g)^-1, I_(N-n-1))]` embeds `GL_n(Q)` in `PE_N(R)`.
3. `PE_N(R)` is finitely presented and simple by hypothesis.

So `GL_n(Q)` embeds in a finitely presented simple group, for every `n >= 2`. ∎

This is conditional. The open premise is a ring problem: find a finitely generated
simple ring `R ⊇ Q` with finitely generated `Λ_N(R)` and the Steinberg/centre
finite-presentation data. The necessary conditions are listed in the premise, and
`rational-scalars-obstruct-fp-elementary-hosts` removes the `K_1 = 0` templates.
