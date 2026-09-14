---
rg: 2
id: kl-p-square-systems-connectedness-proof
kind: route
title: Track the level of each variable letter, then count incidences in a regular bipartite graph
target: kl-p-square-systems-are-connected-after-localization
requires: [kl-p-power-index-reduces-to-p-nonsingular-square-systems, kl-failure-localizes-to-the-coefficient-subgroup]
artifacts:
  - research/artifacts/hl-kl-torsion-pins-2026-09-13.md
---

**1. Gauge.** `t -> t g` sends `<<w>>` onto `<<w'>>` and fixes `G`, so
`G -> G_w` is injective iff `G -> G_(w')` is. Substituting `t = c` into `w-`
equals substituting `t = 1` into `w'-`, because `phi(t g) = c`. So `1` is a root
of `w'`. Conjugating by an element of `G` rotates the word and does not change
injectivity; this puts `w'` in the displayed form. Build the square system for
`w'` with `c = 1`, so `y_q = g_q t g_q^(-1)`.

**2. Localization.** The coefficients of `w'` lie in `G_R`. By
`kl-failure-localizes-to-the-coefficient-subgroup`, a violation over `G` at `w'`
is a violation over the subgroup they generate, hence over `G_R`. So injectivity
of `G_R` gives injectivity of `G`. `H <= G_R`, `G_R/H = R`, and `R` is again a
`p`-group.

**3. Levels.** In route `kl-p-power-index-p-nonsingular-proof`, with `c = 1`:
- the letter `s_j = t` contributes `y_(q phi(s_1...s_(j-1)))`;
- the letter `s_j = t^(-1)` contributes `y_(q phi(s_1...s_j))^(-1)`.

Since `phi(t) = 1`, both indices equal `q L_j` with
`L_j = phi(a_1 ... a_(j-1))`. So the unknown letters of `rho_q` are
`y_(q L_j)^(eps_j)` in order, separated by `H`-letters. The coefficient `a_j`
follows the letter `t^(eps_j)` at coset `x = q L_j` (because `phi(t) = 1`) and
contributes `g_x a_j g_(x phi(a_j))^(-1)`.

*No cancellation.* Two unknown letters can cancel only when they are adjacent
(the `H`-letter between them trivial), have opposite signs, and have equal
indices. Opposite signs mean `eps_j = -eps_(j+1)`, and equal indices mean
`L_(j+1) = L_j`, that is `a_j in H`. The `H`-letter is then
`g_x a_j g_x^(-1)`, which is trivial only if `a_j = 1`. But `w'` is reduced, so
the coefficient between `t` and `t^(-1)` is not `1`. Same-sign neighbours never
cancel. So the set of unknowns occurring in `rho_q` is exactly `q Lambda`.

**4. Incidence.** Equation `q` contains `y_x` iff `x in q Lambda`, iff
`q in x Lambda^(-1)`.
- Both sides of the bipartite incidence graph have `n` vertices, and every
  vertex has degree `|Lambda|`.
- Equations `q, q'` share an unknown iff `q^(-1) q' in Lambda Lambda^(-1)`, so
  the components of equations are the left cosets of
  `S = <Lambda Lambda^(-1)>`.
- `1 = L_1 in Lambda`, so `Lambda ⊆ Lambda Lambda^(-1) ⊆ S`.
- `Lambda` contains every partial product `phi(a_1...a_j)` for `j < k`, so `S`
  contains `phi(a_1), ..., phi(a_(k-1))`. The root condition
  `phi(a_1 ... a_k) = 1` gives `phi(a_k) in S` as well, so `S ⊇ R = Q`, and the
  graph is connected.
- If `R = Q != 1`, some `phi(a_j) != 1`; since `L_1 = 1`, `Lambda` has two
  distinct elements.

*Counting.* Let `T` be a set of `k` equations, `U` the unknowns they contain.
- `T` sends `k |Lambda|` edges into `U`, and each unknown receives at most
  `|Lambda|`, so `|U| >= k`.
- If `|U| = k`, every edge into `U` comes from `T`. Then `T ∪ U` is closed under
  adjacency, hence a union of components, hence everything.
- So `0 < k < n` forces `|U| > k`. In particular the first equation of any
  ordering already contains `|Lambda| >= 2` unknowns.

**5. Degenerate case.**
- `|Lambda| = 1` means all partial products are `1`, i.e. every `phi(a_j) = 1`,
  i.e. `w' in H * <t>`.
- Conversely, if `w' in H * <t>`, all levels are `1`.
- By `kl-failure-localizes-to-the-coefficient-subgroup`, `H -> H_(w')`
  injective implies `G -> G_(w')` injective. Conversely `H <= G`, and
  `ker(H -> H_(w')) <= ker(G -> G_(w'))` through `H * <t> -> G * <t>`.
- At degree `±1`, Klyachko's theorem injects a torsion-free `H`.
