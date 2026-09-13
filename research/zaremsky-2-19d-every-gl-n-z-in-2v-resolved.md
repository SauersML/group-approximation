---
rg: 2
id: zaremsky-2-19d-every-gl-n-z-in-2v-resolved
kind: claim
title: "Zaremsky Problem 2.19(d) resolved: does every GL_n(Z) embed in the Brin-Thompson group 2V?"
---

Part (d) of `zaremsky-2-19-embeddings-into-brin-thompson-groups`, verbatim from
the list, following "Does every GL_n(Z) embed in some mV?": "Maybe even in 2V?"

This claim is the question. It is established only through an answer route,
`zaremsky-2-19d-by-yes` or `zaremsky-2-19d-by-no`. Lane z2-19-glnz-q-2v chooses
the answer claims. Suggested ids: `every-gl-n-z-embeds-in-2v` and
`some-gl-n-z-does-not-embed-in-2v`. Never write a `requires: []` route into this
claim.

## Reading

- GL_n(Z) ≤ GL_(n+1)(Z), so a yes means that GL_n(Z) embeds in 2V for every n.
- A yes to this part implies a yes to part (c).
- GL_2(Z) embeds in V, hence in 2V. The content starts at n = 3.
- An answer no may come from a single n. For example, SL_3(Z) not embedding in
  2V would already give no.

## Couplings

- A yes puts SL_3(Z), which has property (T), inside 2V, so 2V fails the
  Haagerup property.
- If 2V has the Haagerup property, the answer is no.
- Belk–Bleak–Matucci conjecture that a right-angled Artin group `A_Γ` embeds in
  nV exactly when it contains no `Z^(n+1) * Z` (arXiv:1602.08635, Conjecture
  1.7). RAAG subgroups of GL_n(Z) (Hsu–Wise) could therefore obstruct
  embeddings in 2V if that conjecture holds. This lane has not checked which
  RAAGs sit in GL_3(Z) or GL_4(Z).

## Attempts

- 2026-09-13 (lane z2-19-hyperbolic-nv): recorded the reading and the couplings.
  The attack belongs to lane z2-19-glnz-q-2v.
