---
rg: 2
id: char-zero-linear-pbh-via-elementary-coordinates
kind: route
title: Land directly in the elementary group of the coordinate ring, then use the finitely presented self-similar affine host
target: char-zero-linear-groups-satisfy-permutational-boone-higman
requires:
  - linear-groups-embed-in-elementary-coordinate-groups
  - elementary-groups-over-polynomial-s-integers-are-fp
  - affine-extension-of-fp-elementary-group-is-fp
  - polynomial-parameter-affine-groups-are-self-similar
  - fp-self-similar-subgroups-satisfy-permutational-boone-higman
---

This is `char-zero-linear-pbh-via-polynomial-self-similar-hosts` with its steps 1–2 replaced.
Those steps were coordinates in `GL_M(R)`, then `SL_N(R) = E_N(R)`, which cites Suslin and
Weibel. Here they are replaced by `linear-groups-embed-in-elementary-coordinate-groups`, part 2.
That part gives `H ↪ E_N(R)` for `R = Z[1/m][x_1..x_k]` and every large `N`, in particular
`N >= k+4`, using only Gaussian elimination over `K`. Steps 3–5 are unchanged:
- `E_N(R)` is finitely presented;
- `R^N ⋊ E_N(R)` is finitely presented and self-similar at a prime `p ∤ m`;
- part (a) of `fp-self-similar-subgroups-satisfy-permutational-boone-higman` applies.

The route has one fewer literature input than the old one, namely `SK_1(Z[1/m][x]) = 0`.

Lean: `GroupApproximation.BooneHigmanLinear.NoSuslin.charZeroLinearHost_of_elementaryFPFive`,
in `BooneHigmanLinear/CharZero/ElementaryHost.lean`, landed e5e9cd450a and not yet built. It
gives the finitely presented self-similar host from the finite presentation of `E_N(R)` alone.
Lane proof, not reviewed.
