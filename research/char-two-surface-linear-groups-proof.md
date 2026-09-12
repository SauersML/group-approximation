---
rg: 2
id: char-two-surface-linear-groups-proof
kind: route
title: Realize F_2[t_1,t_2][1/h] over a Laurent ring in one factor and the curve ring in the other
target: char-two-surface-linear-groups-satisfy-boone-higman
requires:
  - leavitt-square-unit-group-is-fp-simple-and-acyclic
  - char-two-curve-linear-groups-satisfy-boone-higman
  - char-two-laurent-linear-groups-satisfy-boone-higman
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

This is artifact Lemma 7.1 and Theorem 7.2 at `d <= 2`. Let `H <= GL_n(K)` be
finitely generated.

1. **Reduce to a localized polynomial ring.** Follow Steps 0--2 of
   `char-two-curve-linear-groups-proof`. The entries generate a finite
   extension, of degree `m`, of `F_2(t_1, ..., t_d)` with `d <= 2`. The regular
   representation, then clearing denominators, gives
   `H <= GL_(nm)(F_2[t_1, ..., t_d][1/h])`.
2. **The case `d <= 1`.** `char-two-curve-linear-groups-satisfy-boone-higman`
   embeds `H` in `L^x <= (L ⊗ L)^x`, through `L ⊗ 1`.
3. **The case `d = 2`, localizing in `t_1`.** Let `c ∈ F_2[t_1]` be the leading
   coefficient of `h` in `t_2`. Put `C = F_2[t_1][1/c]` and
   `f = t_2 h / c ∈ C[t_2]`, which is monic of positive degree. Then
   `F_2[t_1, t_2][1/h] ⊆ C[t_2][1/f]`.
4. **Freeness over a Laurent ring.**
   `C[t_2][1/f] ≅ C[g^±][T]/(f(T) - g)`. This is free over `C[g^±]` with basis
   `1, ..., T^(deg f - 1)`, so it embeds unitally in `M_(deg f)(C[g^±])`.
5. **Into `L ⊗ L`.** `C[g^±] = C ⊗ F_2[g^±]`, and:
   - Steps 2--4 of `char-two-curve-linear-groups-proof` put `C` in `L` unitally;
   - `char-two-laurent-linear-groups-proof` puts `F_2[g^±]` in `L` unitally;
   - over a field, the tensor product of the two injections is injective.

   Leaf coordinates in the first factor give `M_k(L ⊗ L) ≅ L ⊗ L`, so
   `H <= GL_(nm deg f)(L ⊗ L) ≅ (L ⊗ L)^x`.
6. **Conclusion.** `leavitt-square-unit-group-is-fp-simple-and-acyclic` makes
   the target finitely presented and simple.
