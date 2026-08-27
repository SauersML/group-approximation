---
rg: 2
id: dictator-is-heavy-in-every-affine-direction
kind: claim
title: A single ambient dictator is heavy in all N-1 affine directions, so no counting bound on the heavy directions can exist
invalidates:
  - glue-lemma-via-parseval-budget-across-directions
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**ESTABLISHED, and it is the cheapest fact in the region.**  Take
`f = X_p` for a single `p in Omega`, and `g = T_rho f = rho X_p`.  For every
`b != 0`,

```text
g|_{D_b} = rho * Y_{[p]_b},
```

a dictator on the quotient coordinate `[p]_b = p + <b>`.  So the coset
`[p]_b` is `(d, rho^2)`-heavy for **every** one of the `N - 1` directions,
with `f` bounded, of degree 1, and exactly noise-invariant up to the
constant `rho`.

**Consequence.**  The number of heavy directions is not bounded by anything,
and no `L^2`, Parseval, entropy or density argument can bound it: the most
benign function in the problem already saturates the count.  Any attack
whose plan is "there cannot be many heavy directions" is dead before it
starts, independently of the memorizer constructions, which need unbounded
functions to make their point.

This is why `affine-orientation-glue-lemma` asks what it asks.  The content
is never scarcity of heavy directions -- it is **concentration of their
centres**.  Here every heavy coset contains the single point `p`, so
`Q = {p}` works with `gamma = 1`, and the lemma is asking whether that
phenomenon is forced.

Recorded as a second, independent invalidator of
`glue-lemma-via-parseval-budget-across-directions`.  The memorizer kill on
that route is about vanishing ambient `L^2` mass carrying maximal
heaviness; this one is blunter and shows the counting plan was never viable
even for bounded low-degree functions.

The proof is `dictator-heavy-in-every-direction-proof`.
