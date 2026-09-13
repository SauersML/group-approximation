---
rg: 2
id: thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2
kind: claim
title: Thompson's group F has no cobounded isometric action on a geodesic space quasi-isometric to H^2
distinct_from:
  thompson-f-has-no-cobounded-action-on-hyperbolic-plane: that claim is only about isometries of H^2 itself, proved by linearity; this claim is about all geodesic spaces quasi-isometric to H^2, whose isometry groups need not be linear, and needs quasi-action rigidity
---

For every geodesic metric space `X` quasi-isometric to the real hyperbolic plane `H^2`,
every isometric action of Thompson's group `F` on `X` has no coarsely dense orbit.
Equivalently: no hyperbolic structure on `F` (in the sense of Abbott–Balasubramanya–Osin)
is representable by an action on a space quasi-isometric to `H^2`. This is the last
sentence of Question 11.4 of arXiv:2406.12982 (Balasubramanya–Fournier-Facio–Zaremsky),
the source of Zaremsky Problem 2.18.

## Attempts

- **Reduction written (2026-09-13, lane z2-18-f-h2-action):** route
  `thompson-f-no-cobounded-qi-h2-action-via-markovic`. The boundary kernel `N` of the
  transported quasi-action either contains `[F,F]` or meets it trivially.
  - If it contains `[F,F]`, the image is abelian and the orbits stay near two quasi-geodesics.
    This case uses only stability of quasi-geodesics.
  - If it meets `[F,F]` trivially, Markovic's theorem makes the boundary group a Möbius group,
    and the Tits alternative contradicts simplicity of `[F,F]`.
  The route fires once its two open import claims are read from their sources:
  - `uniformly-quasisymmetric-circle-groups-are-mobius-conjugates` (Markovic, J. Amer. Math.
    Soc. 19 (2006) 673–715; bibliographic data verified, theorem not re-read);
  - `h2-quasi-isometries-have-uniformly-quasisymmetric-boundary-maps` (classical, not
    re-read).
- **Structure check (consistent with the reduction).** A cobounded action on such an `X` has
  limit set `∂X = S^1`, so it is neither elliptic, horocyclic nor lineal. It is not of general
  type, because `F` has no free subgroups. By arXiv:2406.12982 Theorem A it is quasi-parabolic,
  attached to an endpoint character. The claim says none of these quasi-parabolic structures
  is quasi-isometric to `H^2`, the way the "real place" structure of `BS(1,2)` is.
