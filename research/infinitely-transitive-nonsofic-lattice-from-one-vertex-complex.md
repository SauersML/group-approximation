---
rg: 2
id: infinitely-transitive-nonsofic-lattice-from-one-vertex-complex
kind: route
title: Embed a nonsofic one-vertex square complex group in a Burger-Mozes lattice with dense U(Alt) projections
target: nonsofic-infinitely-transitive-tree-lattice
requires:
  - nonsofic-one-vertex-square-complex-group
  - burger-mozes-infinitely-transitive-tree-groups
---

Conditional route; it fires when `nonsofic-one-vertex-square-complex-group` is established.

1. Let `Z` be the one-vertex VH-T-complex with nonsofic `π_1(Z)`. By item 5 of
   `burger-mozes-infinitely-transitive-tree-groups` (Burger–Mozes, *Lattices in product of
   trees*, Theorem 6.5 and its proof), there is a one-vertex VH-T-complex `X` with
   `π_1(Z) <= Γ := π_1(X)`, where `Γ < U(A_(2n)) × U(A_(2m))` is a cocompact lattice with
   dense projections.
2. Subgroups of sofic groups are sofic, so `Γ` is not sofic.
3. The projection closures are `H_1 = U(A_(2n))` and `H_2 = U(A_(2m))`. By item 4,
   `U(F)^+ = U(F)^(∞)` has index 2 and is locally `∞`-transitive for 2-transitive `F`
   (here `2n, 2m >= 4`). `U(F)` contains `U(F)^+`, so it is non-compact and transitive on
   `∂T`, and item 1 makes it locally `∞`-transitive.

So `Γ` witnesses `nonsofic-infinitely-transitive-tree-lattice`.
