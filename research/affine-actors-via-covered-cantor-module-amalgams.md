---
rg: 2
id: affine-actors-via-covered-cantor-module-amalgams
kind: route
title: Put the input in a finitely presented covered group of Cantor-module automorphisms; amalgamation makes the extension finitely presented and V makes it orbit-finite
target: decidable-groups-embed-in-orbit-finite-affine-actors
requires:
  - decidable-groups-embed-in-covered-cantor-module-actors
  - amalgamated-module-extensions-are-fp
  - cantor-module-thompson-v-product-is-finitely-presented
---

Let `G` be finitely generated with solvable word problem, and `W` a finitely presented
covered group containing `G` (`decidable-groups-embed-in-covered-cantor-module-actors`).
Put `S = M = C(C, F_2)`.

1. **Setting.** `S` is countable, and `W <= Aut(S)` is finitely generated.
2. **`S ⋊ W` is finitely presented.** `S ⋊ V` is finitely presented
   (`cantor-module-thompson-v-product-is-finitely-presented`), and the covering data are
   the remaining hypotheses of `amalgamated-module-extensions-are-fp`.
3. **Finitely many orbits.** `V` is transitive on proper nonempty clopen subsets of `C`
   (item 4 of `leavitt-cantor-module-fp-via-thompson-amalgam`), and over `F_2` every
   `f ∈ M` other than `0` and `1` is the indicator of such a set. So `W ⊇ V` has at most
   three orbits on `S`.
4. **Embedding.** `G <= W <= S ⋊ W`.

These are items 1–3 of the target.
