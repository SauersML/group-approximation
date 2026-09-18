---
rg: 2
id: gl-n-q-bh-via-steinberg-shell-envelope
kind: route
title: A finitely presented shell envelope of St_4(R_L) or St_10(R_L) is simple and contains every GL_n(Q)
target: gl-n-q-embeds-in-fp-simple-group
requires:
  - steinberg-resolvent-shell-envelope-is-finitely-presented
  - shell-cantor-embeddings-are-finite-germ-extensions
  - perfect-input-shell-envelopes-are-simple
  - one-steinberg-group-contains-every-gl-n-q
  - leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1
---

Choose an admissible input `P` and an enumeration `nu` as in
`steinberg-resolvent-shell-envelope-is-finitely-presented`, so that `E_nu` is finitely
presented. Then `P` is `St_4(R_L)`, or `St_N(R_L)` for some `N >= 5` containing every
`GL_n(Q)`, for example `St_10(R_L)`.

- `hat : P -> E_nu` is injective (`shell-cantor-embeddings-are-finite-germ-extensions`).
- `P` is perfect, since `N >= 3`, so `E_nu` is simple
  (`perfect-input-shell-envelopes-are-simple`).
- For every `n >= 1`, `GL_n(Q)` embeds in `P`:
  - for `St_4(R_L)` by `one-steinberg-group-contains-every-gl-n-q`;
  - for `St_10(R_L)` by item 2 of `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1`;
  - for any other admissible rank by admissibility.

So `GL_n(Q) -> P -> E_nu` embeds every `GL_n(Q)` in the one finitely presented simple
group `E_nu`. No twisted Brin--Thompson step and no type (A) action is used.

**Imports.**
- The route never uses finite presentation of `P`, so it does not depend on
  Krstić–McCool's rank-4 theorem, not even for `P = St_4(R_L)`.
- The rank-4 import enters only if `St_4(R_L)` is presented as an instance of the
  universal `perfect-decidable-inputs-have-fp-shell-envelopes`. That use is noted in
  the claim.
- With `P = St_10(R_L)`, finite presentation, where it is wanted, comes from
  `steinberg-groups-of-fp-rings-are-fp-in-rank-five`.
