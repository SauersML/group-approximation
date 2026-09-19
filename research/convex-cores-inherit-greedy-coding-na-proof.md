---
rg: 2
id: convex-cores-inherit-greedy-coding-na-proof
kind: route
title: Helly number 2 for convex subcomplexes puts every crossing of two hyperplanes meeting Y inside Y, so disjoint hyperplanes of Y come from disjoint hyperplanes of X, whose stabilizers already meet finitely
target: convex-cores-inherit-greedy-coding-na
requires:
  - greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs
---

Lane `bh-partials`, lane proof, not reviewed. The facts about median graphs are recalled, not read at source here:
- vertex sets of halfspaces and of convex subcomplexes are convex;
- convex sets of a median graph have the Helly property with Helly number 2.

**Item 1.**
- `Y` is convex, so it is a CAT(0) cube complex whose edges are edges of `X`.
- Two edges of `Y` are dual to the same hyperplane of `Y` iff they are joined by a chain of squares of `Y`. Such a
  chain lies in one hyperplane of `X`, so every hyperplane of `Y` lies in some `H ∩ Y`.
- **Conversely, `H ∩ Y` is a single hyperplane of `Y`.** Let `e = ab` and `e' = a'b'` be edges of `Y` dual to `H`,
  with `a, a' ∈ H^-`.
  - Take a geodesic `γ` from `a` to `a'` inside the convex set `Y ∩ N(H) ∩ H^-`.
  - For each vertex `x` of `γ`, let `x'` be its neighbour across `H`. Only `H` separates `x` from `x'`, so
    `d(x', b') = d(x, b') − 1`. Hence `x'` lies on a geodesic from `x` to `b'`, and `x' ∈ Y` by
    convexity.
  - Consecutive vertices `x, y` of `γ` differ across a hyperplane `L` crossing `H`, since `N(H) ∩ H^-` carries the
    cube structure of `H`. So `x, y, y', x'` span a square of `N(H)`. Its vertices lie in `Y`, so the square lies
    in `Y`.
  - This ladder of squares in `Y` joins `e` to `e'`.
- **Injectivity.** An edge of `Y` is dual to exactly one hyperplane of `X`.

**Item 2.**
- If `H ∩ Y` and `K ∩ Y` cross in `Y`, then `H` and `K` cross in `X`.
- **Conversely**, suppose `H` and `K` cross in `X` and both meet `Y`.
  - For each choice of signs, the three convex sets `Y`, `H^±` and `K^±` pairwise intersect. `Y` meets both sides of
    each hyperplane, and the four quarters of `H, K` are nonempty.
  - By Helly, `Y` meets all four quarters.
  - A CAT(0) cube complex in which two hyperplanes have all four quarters nonempty has them crossing (Sageev). Applied in
    `Y`, `H ∩ Y` and `K ∩ Y` cross.

**Item 3.**
- Let `H ∩ Y` and `K ∩ Y` be disjoint hyperplanes of `Y`. By item 2, `H` and `K` are disjoint in `X`.
- If `q ∈ Q` preserves `H ∩ Y`, then `qH ∩ Y = H ∩ Y`, so `qH = H` by injectivity. Hence
  `Stab_Q(H ∩ Y) ≤ Stab_G(H)`, and likewise for `K`.
- So `Stab_Q(H∩Y) ∩ Stab_Q(K∩Y) ≤ Stab_G(H) ∩ Stab_G(K)`, which is finite by (NA) for `X`.

**The remaining hypotheses of the cube theorem for `(Q, Y)`.**
- `Q` is hyperbolic, being quasiconvex, and `Y` is locally finite.
- `Q` acts cocompactly, and freely on the vertices of `Y`, since `G` acts freely on those of `X`.
- `Q` is non-elementary with trivial finite radical, by assumption. ∎
