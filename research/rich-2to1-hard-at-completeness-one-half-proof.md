---
rg: 2
id: rich-2to1-hard-at-completeness-one-half-proof
kind: route
title: Lift the imperfect-completeness 2-to-1 instances by any orientation, then right-merge into all 2-to-1 maps
target: rich-2to1-hard-at-completeness-one-half
requires: [two-to-two-games-theorem, orientation-lifts-sandwich-2to1-game-values]
---

Fix `eps > 0` and put `eps_0 = eps/2`.

**Step 1 (imported).** `two-to-two-games-theorem` records, through the source's
footnote 2, the 2-to-1 Games Theorem with imperfect completeness. For some
constant `k = k(eps_0)`, `Gap-2-to-1[2k]((1 - eps_0), eps_0)` is NP-hard on
bipartite 2-to-1 games with left alphabet `[2k]` and right alphabet `[k]`. For
the Grassmann instances, the left labels are the functionals on an `l`-space,
the right labels are those on a hyperplane, and `2k = 2^l`.

**Step 2.** Choose any polynomial-time orientation, for example the lexicographic
one: the smaller label of each kernel pair gets bit 0. By item (1) of
`orientation-lifts-sandwich-2to1-game-values`, the lift `U_o` satisfies
`val(G)/2 <= val(U_o) <= val(G)`.

**Step 3.** By item (2) of the same claim, `Psi(U_o)` is fully rich, with
`val(G)/2 <= val(Psi(U_o)) <= 2 val(G)`. It has `|R| (2k)!/2^k` right vertices,
which is polynomial because `k` is constant. For every left vertex and every
incident edge `(u,v)`, a uniform `sigma` makes the kernel pairing of
`sigma o phi_(uv)` uniform, so richness survives edge weights.

**Values.**

* YES: `val(G) >= 1 - eps_0` gives `val(Psi(U_o)) >= (1 - eps_0)/2 >= (1-eps)/2`.
* NO: `val(G) <= eps_0` gives `val(Psi(U_o)) <= 2 eps_0 = eps`.

The composite is polynomial, so NP-hardness transfers. `square`

**Alternative path.** Branch-split 2-to-2 instances
(`unique-games-hard-at-completeness-one-half`), take the bipartite double cover,
and right-merge. This path reaches the same gap with soundness factor 4 when the
2-to-2 constraint graph has no loops. The double-cover bounds
`val(U) <= val(B) <= 2 val(U)` hold for loop-free games. They can fail with
loops: a single fixed-point-free loop has `val(U) = 0` and `val(B) = 1`. The
check script replays them in part (B). The route above avoids the loop
hypothesis.
