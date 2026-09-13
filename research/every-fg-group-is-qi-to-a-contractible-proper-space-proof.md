---
rg: 2
id: every-fg-group-is-qi-to-a-contractible-proper-space-proof
kind: route
title: Restrict the Cayley graph metric to a spanning tree
target: every-fg-group-is-qi-to-a-contractible-proper-space
requires: []
---

Let S be a finite generating set of G and Γ the Cayley graph, with each edge
isometric to [0, 1] and the path metric d_Γ. Γ is connected and locally
finite, so (Γ, d_Γ) is a proper geodesic space and its metric topology is
the CW topology.

Choose a spanning tree T ⊆ Γ, for example a breadth-first tree from the
identity. T is a subcomplex containing every vertex. Put d = d_Γ restricted
to T.

1. **(T, d) is a metric space whose topology is that of the tree T.** The
   metric topology of (T, d) is the subspace topology of T in Γ. A
   subcomplex of a CW complex is closed, and its subspace topology is its
   own CW topology.
2. **T is contractible.** A tree with its CW topology is contractible, since
   it deformation retracts to a vertex along geodesics.
3. **(T, d) is proper.** A closed ball of (T, d) is the intersection of T
   with a closed ball of Γ. That is a closed subset of a compact set, hence
   compact.
4. **(T, d) is quasi-isometric to G.** The inclusion (T, d) → (Γ, d_Γ) is an
   isometric embedding. Its image contains every vertex, so every point of Γ
   lies within 1/2 of it. So T is (1, 1/2)-quasi-isometric to Γ, and Γ is
   quasi-isometric to G with the word metric.

Hence (T, d) is contractible, proper and quasi-isometric to G. The metric d
is not a length metric on T. The distance between two vertices adjacent in
Γ but not in T is 1, while the path between them inside T is longer.
