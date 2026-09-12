---
rg: 2
id: oriented-clifford-skew-rings-sf-from-matrix-lamp-wreath
kind: route
title: Stable finiteness of the matrix-lamp wreath passes to every oriented Clifford skew ring
target: oriented-kun-thom-clifford-skew-rings-are-stably-finite
requires:
  - matrix-lamp-wreath-algebras-are-stably-finite
  - oriented-clifford-skew-rings-embed-in-matrix-lamp-wreath
  - linear-sofic-group-algebra-is-stably-finite
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

- The Kun--Thom group `G` is residually finite, hence sofic, hence `F_p`-linear sofic. So `F_p[G]` is
  stably finite.
- `matrix-lamp-wreath-algebras-are-stably-finite` then makes `B_X` stably finite.
- Proposition 1.1 embeds `A_S` unitally in `B_X`, so matrices over `A_S` embed in matrices over `B_X`.
- A one-sided inverse pair would survive the embedding.
