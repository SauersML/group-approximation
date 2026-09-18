---
rg: 2
id: orientation-lifts-sandwich-2to1-game-values
kind: claim
title: Every orientation lift of a 2-to-1 game is a unique game of value between half and all of the source value, and its right merge is fully rich, so richness and soundness are free and only the completeness of a branch selector is missing
distinct_from:
  unique-constraints-orient-at-most-half-of-a-fiber: that forbids simulating a 2-to-1 merge inside a network of unique constraints over the source right alphabet; this doubles the right alphabet so no merge is simulated, and proves the exact value window [val/2, val] of the lift for every orientation, placing the one-half wall in the right bit rather than in a gadget.
  sd-rich-and-unique-games-sos-gaps-interconvert: that is the right merge Psi from unique games to rich games; this composes Psi with orientation lifts of arbitrary 2-to-1 games and proves the converse, that Psi(U) always carries an orientation whose lift recovers val(U).
  left-preserving-local-richness-wrappers-are-affine-ug-merges: that shows local richness wrappers are merges of a unique game already present; this names the unique game every rich 2-to-1 hardness proof must implicitly supply, an orientation lift, and shows its completeness is the only parameter at stake.
  rich-2to1-conjecture-is-equivalent-to-ugc: that is the BKM equivalence through the long-code noise test; this is a test-free reformulation at the level of orientations, with explicit value windows and no analytic step.
artifacts:
  - experiments/orientation-lift-2026-09-17/check_orientation_lift.py
---

**ESTABLISHED.**

*Setting.* `G` is a weighted bipartite 2-to-1 game with left alphabet `[2k]`,
right alphabet `[k]`, and projections `p_e : [2k] -> [k]`, each exactly 2-to-1.
An **orientation** `o = (o_e)` picks for every edge a map `o_e : [2k] -> {0,1}`
that is injective on each fibre of `p_e`. So it names one "upper" element per
kernel pair. The **orientation lift** `U_o` is the unique game on the same
weighted graph. Its right alphabet is `[k] x {0,1}`, identified with `[2k]`, and
edge `e` carries the bijection `a -> (p_e(a), o_e(a))`.

1. **Sandwich.** For every orientation `o`,
   ```text
   val(G)/2  <=  val(U_o)  <=  val(G).
   ```
   Both ends are attained by some `G, o`.
2. **Free richness.** `Psi(U_o)`, the BKM right merge, is a fully rich 2-to-1
   game with
   ```text
   val(G)/2  <=  val(U_o)  <=  val(Psi(U_o))  <=  2 val(U_o)  <=  2 val(G).
   ```
3. **Completeness is a branch statistic.** For a left labelling `L`, let
   `w_v(L, b)` be the weight of edges `e = (u,v)` that `L` satisfies in `G`, with
   the best right label, and whose branch is `o_e(L_u) = b`. Then
   `val(U_o) = max_L sum_v max_b w_v(L, b)`. So `U_o` loses exactly the minority
   branch mass at each right vertex.
4. **Converse (every unique game is some lift).** Let `U` be a bipartite unique
   game with alphabet `[2k]`. On `Psi(U)`, the edge `(u, (v, sigma))` with
   constraint `sigma o phi_(uv)` carries the **canonical orientation**: the bit
   is 1 iff `phi_(uv)(a)` is the larger element of its `sigma`-fibre. Then
   `val(U_canonical) >= val(U)`.
5. **Linear normal form.** Let `p_e` be an affine surjection `F_2^l -> F_2^(l-1)`
   with kernel `{0, chi_e}`. Then for any linear `lambda_e` with
   `lambda_e(chi_e) = 1`, every orientation has the form
   `o_e(s) = lambda_e(s) xor g_e(p_e(s))` for a unique function `g_e`. In the
   restriction case, left labels are the linear functionals on an `l`-dimensional
   `L`, right labels are those on a hyperplane `L' < L`, and `p_e` is
   restriction. Take `lambda_e(s) = s(x_e)` for any fixed `x_e in L \ L'`. On an
   honest labelling `s = A|_L` the branch is `A(x_e) xor g_e(A|_(L'))`. That is,
   the assignment's value on a direction the right vertex does not see,
   corrected by a function of what it does see. Folding offsets only change
   `g_e`.

**Consequences.**

* **(a) Richness and soundness transfer for free, completeness does not.** Take
  any polynomial-time reduction `R` to `Gap-2-to-1[1-eta, s]` together with a
  polynomial-time orientation `o`. If every YES output has
  `val(U_o) >= c`, then `x -> Psi(U_o(R(x)))` proves
  `Gap-Rich-2-to-1[c, 2s]` NP-hard, and `x -> U_o(R(x))` proves `Gap-UG[c, s]`.
  With `c = 1/2 - eta/2` this needs no selector at all
  (`rich-2to1-hard-at-completeness-one-half`).
* **(b) The single-parameter reformulation.** `rich-2to1-games-conjecture`
  holds iff for every `eps > 0` some polynomial-time reduction to
  `Gap-2-to-1[1-eps, eps]` comes with a polynomial-time orientation whose YES
  lifts have value `>= 1 - eps`. One direction is (a). For the other, the
  conjecture gives UGC by `rich-2to1-conjecture-is-equivalent-to-ugc`, applied
  at `eps/2`. UGC instances are two-prover games, so they are bipartite. To make
  the alphabet even, replace `[K]` by `[K] x {0,1}` with constraints
  `phi x id`; this changes no value. Then (4) supplies the orientation on
  `Psi(U)`. Its YES lifts have value `>= 1 - eps/2`, and its NO value is
  `<= 2 (eps/2) = eps` by (2).
* **(c) What a selector must do.** By (3), a selector beats the random-bit
  floor `1/2` exactly when, on YES instances, the branches of satisfied edges
  are biased at the typical right vertex. By (5), on linear instances such as
  the DKKMS Grassmann games this means predicting an assignment's values on the
  new direction of each neighbouring subspace. This is the quantity the open
  node `efficient-branch-selector-on-proved-2to1-instances` asks for.

This neither proves nor refutes UGC.

DERIVATION orientation-lifts-sandwich-2to1-game-values-proof
