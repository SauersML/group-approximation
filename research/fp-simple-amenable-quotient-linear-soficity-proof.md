---
rg: 2
id: fp-simple-amenable-quotient-linear-soficity-proof
kind: route
title: Instability of the group algebra is instability of the group, which for a simple group is linear soficity
target: fp-simple-group-algebra-amenable-quotient-gives-linear-soficity
requires: [amenable-f-g-quotient-ideal-makes-algebra-rank-unstable, fp-group-rank-stability-equals-group-algebra-rank-stability, fp-simple-group-not-linear-sofic-iff-rank-stable]
---

1. **`F[G]` is finitely presented.** If `G = <x_1,...,x_d | P_1,...,P_r>`, then
   `F[G] = F<x, y> / <Q_i - 1, x_j y_j - 1, y_j x_j - 1>`, with `Q_i` obtained from `P_i` by replacing `x_j^(-1)` with
   `y_j`. This is the presentation used in the proof on `fp-group-algebra-rank-stability-citation`.
2. **`F[G]` is not rank-stable.** The ideal `I` meets the hypotheses of
   `amenable-f-g-quotient-ideal-makes-algebra-rank-unstable`.
3. **`G` is not rank-stable over `F`.** Use `fp-group-rank-stability-equals-group-algebra-rank-stability`.
4. **`G` is `F`-linear sofic.** This is (a) <=> (b) of item 1 of `fp-simple-group-not-linear-sofic-iff-rank-stable`.
