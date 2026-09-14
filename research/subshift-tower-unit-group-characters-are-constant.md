---
rg: 2
id: subshift-tower-unit-group-characters-are-constant
kind: claim
title: Characters of EL_3(LC(X,F_2)⋊Z) are constant off the identity on tower unit groups, which generate
artifacts:
  - research/artifacts/sk-characters-rigidity-b-proof-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `X` is an infinite minimal Cantor system (an infinite minimal subshift, for instance), `R = LC(X,F_2) ⋊_T Z` and `G = EL_3(R)`.
- For `y ∈ X`, choose Kakutani–Rokhlin partitions `𝒫_n` whose bases `B_n` shrink to `y` and whose levels generate the topology, with each tower of `𝒫_{n+1}` a concatenation of towers of `𝒫_n`.
- The tower algebras `A(𝒫_n) = span{e_{T^aC}u^{a−b}} ≅ ⊕_C M_{h_C}(F_2)` increase.
- `L_y := ⋃_n GL_3(A(𝒫_n)) = ⋃_n ∏_C GL_{3h_C}(F_2)` is a locally finite subgroup of `G`.

**Statement.**
1. **Generation.** If `y ≠ y'`, then `G = ⟨L_y, L_{y'}⟩`.
2. **Constancy.** For every character `χ` of `G` (positive definite class function, `χ(e) = 1`) there is `c ∈ [0,1]` with `χ(h) = c` for all `h ∈ L_y ∖ {1}`.
3. **Independence of y.** `c = χ(e_12(e_P))` for every nonempty clopen `P`, so `c` does not depend on `y`.

Route: `subshift-tower-unit-group-characters-are-constant-proof`.

**Why it holds.**
- A nontrivial `h ∈ GL_3(A(𝒫_m))` becomes block diagonal in every factor `GL_N(F_2)` of `GL_3(A(𝒫_n))`, with a number of nontrivial blocks proportional to `N`.
- The Larsen–Tiep bound, together with elementary class-size and degree bounds, makes every nontrivial normalized irreducible character small at such elements.
- So `χ(h)` equals the limit of the trivial-representation weights.

Contrast: for the natural limit `GL_∞(F_q)` the support of a fixed element stays bounded along the limit, and the Thoma–Skudlarek characters `q^{−m·rank(g−1)}` survive.
