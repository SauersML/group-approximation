---
rg: 2
id: every-type-fpn-group-is-of-type-fhn
kind: claim
title: "Every group of type FP_n acts freely and cocompactly on an (n-1)-acyclic CW complex, for every n"
---

For every `n ≥ 0` and every group `G` of type `FP_n` (over `ℤ`) there is a
CW complex `X` with `H̃_i(X; ℤ) = 0` for `i ≤ n−1`, on which `G` acts freely
and cellularly with finitely many orbits of cells.

This is the affirmative answer to Zaremsky Problem 1.4
(`zaremsky-1-04-type-fpn-equals-type-fhn`). A free action is proper, so this
statement answers the printed question with the printed "proper" reading.

## Attempts

- `n ≤ 2`: true. For `n = 2`, take a Cayley graph `Γ` for a finite
  generating set. Then `H_1(Γ)` is the relation module, which is finitely
  generated over `ℤG` exactly when `G` is of type `FP_2`. Attach one
  `G`-orbit of 2-cells along a closed edge loop for each of finitely many
  module generators; the result is connected with `H_1 = 0`.
- `n = 3` is equivalent to: every group of type `FP_3` is `Q/P` with `Q`
  finitely presented and `P` superperfect (see the root's Attempts). The
  attempt dies at `H_2(P)`, the cokernel of the Hurewicz map of the
  `G`-cover of a presentation complex. Every construction tried so far that
  kills part of `H_2(P)` creates new non-spherical `H_2` classes.
- `n ≥ 4`: after 3-cells are attached, the cokernel of Hurewicz in degree 3
  involves `H_3(P)` and `H_1(P; π_2)`, through the spectral sequence of the
  universal cover. No attack yet.
