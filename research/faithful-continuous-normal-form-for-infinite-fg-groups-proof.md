---
rg: 2
id: faithful-continuous-normal-form-for-infinite-fg-groups-proof
kind: route
title: Pad each representative with a block code for a dense Bernoulli orbit, longer for longer elements
target: faithful-continuous-normal-form-for-infinite-fg-groups
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

**Step 1: two identity blocks coding binary digits.**  Take `X` finite
symmetric generating `G`.  As `G` is infinite, `X` has two distinct letters;
fix distinct `a, b in X` and set

    U_0 = a a^{-1} ,     U_1 = b b^{-1} .

Both represent `1`, both have length 2, and they have distinct first letters,
so `0 |-> U_0`, `1 |-> U_1` gives an injective block code `C : {0,1}* -> X*`
and a topological embedding `C_inf : {0,1}^N -> X^omega`.

**Step 2: a faithful compact action with a dense orbit.**  Let `Y = {0,1}^G`
with the Bernoulli shift.  It is faithful: for `g != 1` pick `y` with
`y(1) != y(g)`; then `(g·y)(g) = y(1) != y(g)`.  For a dense orbit, enumerate
the finite cylinder conditions `(F_i, p_i)` with `F_i ⊆ G` finite and
`p_i : F_i -> {0,1}`, and choose `h_i in G` recursively so that the sets
`h_i F_i` are pairwise disjoint — possible because at stage `i` only finitely
many choices are forbidden and `G` is infinite.  Define `y_0` to realize the
translated pattern on each `h_i F_i` and arbitrarily elsewhere; then some
translate of `y_0` meets every cylinder, so its orbit is dense.  Fix an
enumeration `G = {e_0, e_1, …}`, put `theta(y) = (y(e_0), y(e_1), …)` and
`iota = C_inf ∘ theta`.

**Step 3: pad by a prefix that grows with word length.**  Let
`rho(g) = |g|_X`, whose sublevel sets are finite, let `y_g = g · y_0`, and
choose any word `r_g` representing `g`.  Set

    l_g = C( first rho(g) digits of theta(y_g) ) · r_g .

The prefix represents `1`, so `l_g` represents `g`, and distinct elements get
distinct words because a word has one value in `G`.  So
`L = { l_g : g in G }` is a set of normal forms.

**Step 4: the boundary is the shift space.**  (⊆) If `l_{g_n} -> z` with the
`g_n` distinct then `rho(g_n) -> infinity`, since `rho` has finite sublevel
sets.  So for each `k`, once `rho(g_n) >= k` the first `2k` letters of
`l_{g_n}` are its first `k` code blocks, and convergence stabilizes them;
hence `z` is an in-phase infinite concatenation of `U_0, U_1`, i.e.
`z = iota(y)` for a unique `y`.  (⊇) Fix `y` and `k` and let `V_k` be the
cylinder of configurations agreeing with `y` at `e_0,…,e_{k-1}`.  Splitting
`V_k` into disjoint nonempty subcylinders and applying density to each shows
`{ g : g·y_0 in V_k }` is infinite, so it contains some `g_k` with
`rho(g_k) >= k`; then `l_{g_k}` agrees with `iota(y)` on its first `k`
blocks, and `l_{g_k} -> iota(y)`.

**Step 5: continuity and faithfulness.**  Define `g · iota(y) = iota(g·y)`.
If `l_{h_n} -> iota(y)` then by Step 4 `rho(h_n) -> infinity` and
`h_n · y_0 -> y`.  Left multiplication by `g` is a bijection of `G`, so
`g h_n` escapes every finite set and `rho(g h_n) -> infinity`; continuity of
the Bernoulli action gives `g h_n · y_0 -> g · y`; and the prefix argument of
Step 4 then gives `l_{g h_n} -> iota(g·y)`.  Boundary points are handled by
continuity of the Bernoulli action directly, and points of `L` are isolated,
so sequential continuity suffices in this metrizable space; applying the
argument to `g^{-1}` makes the maps homeomorphisms.  The boundary action is
conjugate via `iota` to the Bernoulli shift, hence faithful.  ∎

## One repair to the argument as it arrived

The source's density step is garbled — it argues by cases on whether the
stabilizer of `y_0` is infinite, which is not what is needed.  The clean
reason `{ g : g·y_0 in V_k }` is infinite is subcylinder splitting plus
density, as in Step 4 above: `V_k` contains infinitely many pairwise disjoint
nonempty open subsets, each of which meets the dense orbit.  The conclusion
is unaffected.

## Where the construction is deliberately wasteful

The prefix length `rho(g)` is chosen only so that it tends to infinity along
any sequence of distinct elements while remaining computable from `g`; any
proper function of `g` would do.  Nothing in the argument tries to keep `L`
small, regular, or prefix-closed, and that is exactly why the result carries
no automaticity — see the parking note on the target claim.
