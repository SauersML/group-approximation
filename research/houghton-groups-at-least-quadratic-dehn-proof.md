---
rg: 2
id: houghton-groups-at-least-quadratic-dehn-proof
kind: route
title: Houghton groups are not hyperbolic, so the gap theorem forces a quadratic lower bound
target: houghton-groups-have-at-least-quadratic-dehn-function
requires: []
---

Let `n >= 3`. By Brown, `H_n` is finitely presented (Lee, arXiv:1212.0257,
Theorem C gives an explicit presentation), so its Dehn function is defined.

1. `H_n` is not hyperbolic. The kernel `Sym_fin(Y_n)` of the translation map
   is an infinite subgroup in which every element has finite order. In a
   hyperbolic group every infinite subgroup contains an element of infinite
   order (Gromov; see Ghys–de la Harpe, *Sur les groupes hyperboliques
   d'après Mikhael Gromov*, Chapter 8), so `H_n` is not hyperbolic.
2. Isoperimetric gap (Gromov; proofs by Ol'shanskii 1991, Bowditch 1995,
   Papasoglu 1995): for a finitely presented group, either `δ ≼ x`, which
   happens exactly when the group is hyperbolic, or `x^2 ≼ δ`.
3. By 1 and 2, `x^2 ≼ δ_(H_n)(x)`.
