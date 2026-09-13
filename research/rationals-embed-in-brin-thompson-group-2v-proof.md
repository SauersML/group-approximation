---
rg: 2
id: rationals-embed-in-brin-thompson-group-2v-proof
kind: route
title: A mixed-radix odometer in the second coordinate gives an infinite-order element of 2V roots of every order
target: rationals-embed-in-brin-thompson-group-2v
requires: []
---

**Setup.** `C = {0,1}^ω`. For a finite word `u`, `uC` is the cone of words
beginning with `u`. The group `2V` consists of the homeomorphisms `f` of
`C × C` for which there are finitely many rectangles `u_i C × u'_i C`
partitioning `C × C`, and words `v_i, v'_i`, such that the rectangles
`v_i C × v'_i C` also partition `C × C` and `f(u_i w, u'_i w') = (v_i w, v'_i w')`
for all `w, w'` (Brin; Belk–Bleak–Matucci, arXiv:1602.08635, §3).

- **(O1)** Suppose finitely many cones `Y_j` partition `C`, finitely many cones
  `Y'_j` partition `C`, `y_j` and `y'_j` are their prefixes, and `g_j ∈ V`. Then
  the map `(x, y_j w) ↦ (g_j(x), y'_j w)` lies in `2V`. Refine each rectangle
  `C × Y_j` by the domain partition of `g_j`.
- **(O2)** Define `t ∈ V` by `t(00w) = 0w`, `t(01w) = 10w`, `t(1w) = 11w`. Both
  `{00, 01, 1}` and `{0, 10, 11}` are complete prefix codes. Since
  `t^k(01w) = 1^k 0 w` for `k >= 1`, the element `t` has infinite order. Any
  other infinite-order element of `V` works the same way.

**Digit codes.** For `r >= 2`, let `c_{r,i} = 1^i 0` for `0 <= i <= r-2` and
`c_{r,r-1} = 1^(r-1)`. These `r` words form a complete prefix code: every
infinite word begins with exactly one of them. So for each `n >= 1` every
`y ∈ C` factors uniquely as

`y = c_{2,d_1} c_{3,d_2} ⋯ c_{n+1,d_n} w`, with `d_i ∈ {0, …, i}` and `w ∈ C`.

Put `N_n(y) = Σ_{i=1}^{n} d_i · (n+1)!/(i+1)!`. This is the mixed-radix value
of the digits, with `d_i` in radix `i + 1` and `d_n` least significant. It gives
a bijection from digit tuples to `{0, …, (n+1)! − 1}`, and
`N_n(y) = (n+1)·N_{n−1}(y) + d_n`, with `N_0 = 0`.

**The elements.** Put `s_0 = t × id`. For `n >= 1` define

`s_n(x, y) = (t^q(x), c_{2,d'_1} ⋯ c_{n+1,d'_n} w)`,

where `N_n(y) + 1 = q·(n+1)! + N'` with `q ∈ {0,1}`, and `d'` are the digits of
`N'`. The `(n+1)!` rectangles `C × c_{2,d_1}⋯c_{n+1,d_n}C` are permuted by
prefix replacement in `y`. The element `t` is applied in `x` only on the
rectangle with `N_n = (n+1)! − 1`. So `s_n ∈ 2V` by (O1). By induction on `k`,

`s_n^k(x, y) = (t^{⌊(N_n(y)+k)/(n+1)!⌋}(x), digits of (N_n(y)+k) mod (n+1)!)`.

**Relation `s_n^{n+1} = s_{n−1}` for `n >= 1`.** Write `M = N_{n−1}(y)`, so
`N_n(y) + n + 1 = (n+1)(M+1) + d_n`.
- The last digit `d_n` is unchanged.
- The value of `(d_1, …, d_{n−1})` becomes `M + 1` modulo `n!`.
- Since `N_n(y) <= (n+1)! − 1`, at most one wrap occurs. It occurs exactly when
  `(n+1)(M+1) + d_n >= (n+1)!`. Because `d_n <= n` and `M + 1 <= n!`, that is
  exactly when `M = n! − 1`.

So `s_n^{n+1}` adds `1` to the value of the first `n−1` digits modulo `n!`,
applies `t` in `x` exactly on overflow, and keeps `c_{n+1,d_n}` as part of the
tail. That is the definition of `s_{n−1}`, which parses
`y = c_{2,d_1}⋯c_{n,d_{n−1}} w'` with `w' = c_{n+1,d_n} w`. For `n = 1` it reads:
`s_1` toggles `d_1` and applies `t` when `d_1` goes from `1` to `0`, so
`s_1^2 = t × id = s_0`.

**Conclusion.** `s_0` has infinite order, so each `s_n` has infinite order, and
`⟨s_{n−1}⟩ = ⟨s_n^{n+1}⟩ <= ⟨s_n⟩`. The maps `⟨s_n⟩ → (1/(n+1)!)Z`,
`s_n^j ↦ j/(n+1)!`, are isomorphisms. They are compatible with the inclusions,
because `s_{n−1} = s_n^{n+1} ↦ (n+1)/(n+1)! = 1/n!`. Hence

`R = ∪_{n>=0} ⟨s_n⟩ ≅ ∪_{n>=0} (1/(n+1)!)Z = Q`,

and `R <= 2V`. For `n >= 2`, `2V` embeds in `nV` by acting on the first two
coordinates of `C^n` and trivially on the rest. ∎

**Model tests.**
- Replacing `t` by any infinite-order `g ∈ V` shows that `g × id` is infinitely
  divisible in `2V`.
- Replacing `t` by `id` gives a copy of the Prüfer-like torsion union
  `∪ Z/(n+1)!`, which is the locally finite group `Q/Z`, as expected.
- The construction uses the second coordinate essentially, consistent with
  Higman's theorem that `V` has no element of infinite order with roots of
  unbounded order.
