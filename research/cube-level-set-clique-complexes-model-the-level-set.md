---
rg: 2
id: cube-level-set-clique-complexes-model-the-level-set
kind: claim
title: A group acting vertex-transitively on a level set of a CAT(0) cube complex has a Rips complex homotopy equivalent to that level set
artifacts:
  - research/artifacts/zp-cube-level-set-rips-2026-09-13.md
---

Let `X` be a locally finite, finite-dimensional CAT(0) cube complex and
`h: X → R` a map that is affine on cubes, integer-valued on vertices, with
`|h(u) − h(v)| <= 1` on edges. Put `L = h^{-1}(0)` and `V_0 = L ∩ X^(0)`. Let
`K` be the simplicial complex on `V_0` whose simplices are the finite nonempty
subsets of `V_0` lying in one cube, and `Θ` the graph on `V_0` joining distinct
vertices that lie in a common cube.

1. `K = Flag(Θ)` (Helly property of cubes).
2. `|K| ≃ L` (nerve theorem, applied to cube-indexed covers of both).
3. If a group `N` acts on `X` by cubical automorphisms preserving `h`, freely
   and transitively on `V_0`, then with
   `T = {g ≠ 1 : v_0` and `g v_0` lie in a common cube`}` we get
   `Flag(Cay(N,T)) ≅ K ≃ L`. So if `L` is (n−1)-connected, `N` has an
   (n−1)-connected Rips complex (`R_1(N,T)`).

**Scope and credit.** For `h ≡ 0` and `N` acting vertex-transitively on `X`
(e.g. a right-angled Artin group on its Salvetti universal cover), item 3
says `N` has a contractible Rips complex for the generating set of products
over cliques. That case is known: Chalopin–Chepoi–Genevois–Hirai–Osajda,
*Helly groups*, Theorem 4.1 and Lemma 5.20, as cited in Hulbert–Zaremsky
arXiv:2608.25614 and Li–Sánchez Saldaña arXiv:2608.24279; not re-read here.
The level-set form with `h ≠ 0`, which reaches kernels such as
Bestvina–Brady groups, was not found in Zaremsky arXiv:1812.10976,
Hulbert–Zaremsky arXiv:2608.25614 or Li–Sánchez Saldaña arXiv:2608.24279 (the
check was bounded).

**Limits.** An infinite group with property (T) cannot act freely on the
vertices of a CAT(0) cube complex, since such actions have a global fixed
point (Niblo–Reeves). So this route to Zaremsky Problem 4.4 never reaches
infinite Kazhdan groups of type `F_n`.

Proof: `cube-level-set-clique-complexes-model-the-level-set-proof`.
