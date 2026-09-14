---
rg: 2
id: acyclic-subcomplex-pi1-nonhyperlinear-proof
kind: route
title: Kill the fundamental group at a finite stage and apply Nitsche--Thom Theorem 1.2 to the resulting system
target: acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear
requires:
  - kervaire-laudenbach-holds-for-hyperlinear
artifacts:
  - research/artifacts/hl-eg-bestvina-brady-2026-09-14.md
---

Let `Y` be a contractible 2-dimensional CW complex, `K ⊆ Y` a finite connected subcomplex with
`H_1(K) = 0`, and `G = π_1(K)`. Suppose `G` is hyperlinear. We show `G = 1`.

**Step 1: a finite stage kills G.** `K` is finite, so `G` is finitely generated. Represent the
generators by loops in `K`. Each loop is null-homotopic in the simply connected `Y` through a
compact null-homotopy, and a compact subset of a CW complex lies in a finite subcomplex. So there
is a finite connected subcomplex `Z' ⊆ Y` containing `K` such that `G → π_1(Z')` is trivial.

**Step 2: H_2(Z') = 0.** `Z'` and `Y` are 2-dimensional, so `H_2(Z') = ker(∂_2 on C_2(Z'))`.
This is contained in `ker(∂_2 on C_2(Y)) = H_2(Y) = 0`.

**Step 3: normal form.** Every vertex of `Z'` outside `K` is joined to `K` by edge paths, since
`Z'` is connected. Choose a forest `T` of edges not in `K` that contains every such vertex, and
in which each component meets `K` in exactly one vertex. Collapsing each component of `T` to its
vertex in `K` is a homotopy equivalence rel `K`.
- The result is `Z'' = K ∪ (a 1-cells) ∪ (b 2-cells)`, with all new 1-cells attached at vertices
  of `K`.
- `H_2(Z'') = 0`, and `G → π_1(Z'')` is trivial.
- Fix a basepoint in `K` and paths in `K` to the endpoints of the new 1-cells. The new 1-cells
  become free generators `x_1, ..., x_a`, and each 2-cell reads a word `w_j ∈ F_a * G`. Van
  Kampen gives `π_1(Z'') = (G * F_a) / <<w_1, ..., w_b>>`.

**Step 4: the exponent-sum matrix is injective.** Consider the exact sequence of the pair
`(Z'', K)`: `H_2(K) → H_2(Z'') → H_2(Z'', K) → H_1(K)`. The outer terms are `0` and `0`, and
`H_2(Z'') = 0`, so `H_2(Z'', K) = 0`.
- The relative cellular complex is `Z^b → Z^a`. The relative boundary of the `j`-th 2-cell counts,
  with sign, its passages through each new 1-cell. That is the `j`-th row of the exponent-sum
  matrix `E` of `ε(w_1), ..., ε(w_b)`, where `ε: F_a * G → F_a` kills `G`.
- So `ker E = 0`.
- The presentation complex of `<x_1, ..., x_a | ε(w_1), ..., ε(w_b)>` has one vertex, so its
  second homology is `ker E = 0`.

**Step 5: Nitsche--Thom.** By `kervaire-laudenbach-holds-for-hyperlinear` (Nitsche--Thom,
Theorem 1.2, J. Group Theory 25 (2022) 1--10), the system `w_1, ..., w_b` is solvable in a group
`H` containing `G`: "if the presentation complex of `<x_1,...,x_n | epsilon(w_1),...,epsilon(w_k)>`
has trivial second homology, the system is solvable in a group `H` containing `G`".
- A solution `h ∈ H^a` defines `G * F_a → H`, identity on `G` and `x_i ↦ h_i`. It kills every
  `w_j`, so it factors through `π_1(Z'')`.
- Its restriction to `G` is injective, so `G → π_1(Z'')` is injective.
- By Step 3 that map is trivial. Hence `G = 1`.

**Finite groups are hyperlinear.** The left regular representation embeds a finite group `G` in
`U(|G|)`, which is a (constant) metric ultraproduct of unitary groups. Nitsche--Thom also state
the finite case separately: "if `G` is finite, `H` can be taken finite".

**Trust surface.** Only Nitsche--Thom Theorem 1.2 is imported, from the primary PDF read on
2026-08-14 (`kervaire-laudenbach-holds-for-hyperlinear-citation`). Steps 1--4 are elementary and
complete here.
