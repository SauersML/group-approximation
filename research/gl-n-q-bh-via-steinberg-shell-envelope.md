---
rg: 2
id: gl-n-q-bh-via-steinberg-shell-envelope
kind: route
title: A finitely presented shell envelope of St_4(R_L) is simple and contains every GL_n(Q)
target: gl-n-q-embeds-in-fp-simple-group
requires:
  - steinberg-resolvent-shell-envelope-is-finitely-presented
  - shell-cantor-embeddings-are-finite-germ-extensions
  - perfect-input-shell-envelopes-are-simple
  - one-steinberg-group-contains-every-gl-n-q
---

Let `P = St_4(R_L)` and choose `nu` as in
`steinberg-resolvent-shell-envelope-is-finitely-presented`, so `E_nu` is finitely
presented.

- `hat : P -> E_nu` is injective (`shell-cantor-embeddings-are-finite-germ-extensions`).
- `P` is perfect, so `E_nu` is simple (`perfect-input-shell-envelopes-are-simple`).
- For every `n >= 1`, `GL_n(Q)` embeds in `P` (`one-steinberg-group-contains-every-gl-n-q`).

So `GL_n(Q) -> P -> E_nu` embeds every `GL_n(Q)` in the one finitely presented simple
group `E_nu`. No twisted Brin--Thompson step and no type (A) action is used.
