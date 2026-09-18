---
rg: 2
id: unique-games-holonomy-shift-reduction-proof
kind: route
title: Tree-gauge the unique game, read the holonomy group off the non-tree edges, split by orbits, and identify each abelian orbit action with its regular representation; compose with Bafna--Minzer for the corollaries
target: unique-games-reduce-to-shifts-over-their-holonomy-group
requires:
  - affine-ug-easy-on-globally-hypercontractive-graphs
artifacts:
  - experiments/ugc-holonomy-shift-2026-09-17/check_holonomy_reduction.py
---

A direct proof. The only import is Bafna--Minzer Definition 1.4 and Theorems
1.6--1.8, through `affine-ug-easy-on-globally-hypercontractive-graphs`, and only
for Corollary BM.

**1. Gauge.** Put `sigma'_v = g_v(sigma_v)`. Then `sigma_v = pi_e(sigma_u)`
iff `sigma'_v = g_v pi_e g_u^(-1)(sigma'_u)`. So each edge is satisfied by
`sigma` iff it is satisfied by `sigma'`, and `sigma -> sigma'` is a bijection.
The relaxation statement is the same, since relabeling permutes the vector
variables `z(v, i)` within each vertex. For a closed walk at `r`, the gauged
product telescopes to `g_r (pi_(e_m) ... pi_(e_1)) g_r^(-1)`. A path `P` from
`r` to `r'` gives `Mon_(r')(U) = pi_P Mon_r(U) pi_P^(-1)`.

**2. Tree gauge.** Orient `T` away from `r`. Set `g_r = id` and, for a tree edge
`(u, v)` with `u` closer to `r`, set `g_v = g_u pi_e^(-1)`. Then
`pi_e^g = g_v pi_e g_u^(-1) = id`, and `g` is unique given `g_r`. By step 1 with
`g_r = id`, `Mon_r(U) = Mon_r(U^g)`. In `U^g`, the product along any closed walk
is the product of the non-tree `pi_e^g` it traverses, so `Mon_r(U^g)` lies in
the group they generate. Conversely, the fundamental cycle of a non-tree edge
`e = (u, v)` (tree path `r -> u`, then `e`, then tree path `v -> r`) has product
exactly `pi_e^g`. So the generated group equals `Mon_r(U)` and contains every
gauged constraint, the tree ones being `id`.

**3. Subgroup criterion.** (<=) If `h Mon_r(U) h^(-1) <= Gamma`, compose the
tree gauge with the constant gauge `h`. Every constraint becomes
`h pi_e^g h^(-1) in Gamma`. (=>) If `U^(g')` has all constraints in `Gamma`,
then every closed-walk product of `U^(g')` is in `Gamma`, so
`Mon_r(U^(g')) = g'_r Mon_r(U) g'_r^(-1) <= Gamma`.

**4. Orbit split.** In the tree gauge, every constraint is in `H = Mon_r(U)`,
so it maps each orbit `O_i` onto itself. A labeling of `U_i` is a labeling of
`U^g`, which gives `max_i val(U_i) <= val(U)`. For the upper bound, take a
labeling `sigma` of `U^g`. A satisfied edge `(u, v)` has `sigma_v` in the orbit
of `sigma_u`. Let `E_i` be the satisfied edges with `sigma_u in O_i`. Define
`sigma^(i)` as `sigma_v` where `sigma_v in O_i`, and as a fixed point of `O_i`
elsewhere. It satisfies every edge of `E_i` in `U_i`. So
`val(U) = sum_i w(E_i) <= sum_i val(U_i)`.

**5. Shift form.** Let `A = A_i`, which is transitive on `O = O_i`. If `A` is
abelian, then for `a in Stab(o)` and any `x = b(o)`,
`a(x) = a b(o) = b a(o) = b(o) = x`. So `Stab(o)` fixes `O` pointwise and is
trivial in `A`, and the action is regular. In general, assume regularity. Then
`phi(a) = a(o)` is a bijection `A -> O`, by transitivity and trivial
stabilizer. For `gamma in A`,
`gamma(phi(a)) = gamma a (o) = phi(gamma a)`. So in the coordinates `phi^(-1)`
the constraint `sigma_v = gamma_e(sigma_u)` reads `x_v = gamma_e x_u`, a shift
by `gamma_e` in `A`. If `A = <h>` is cyclic of order `m = |O|`, then
`h^j -> j` identifies `A` with `Z_m`, and the constraint is `x_v = x_u + b_e`,
which is Bafna--Minzer Definition 1.4 with `q = m`.

**6. Complexity.** BFS gives `g` with `O(|V|)` compositions of length-`k`
permutations. Orbits come from union-find over the `<= |E|` generators. For
`O_i`, close the restricted generators under composition. When `A_i` is
regular it has exactly `|O_i|` elements, so the closure stops within
`|O_i| <= k` elements, using `O(k |E|)` compositions. If it exceeds `|O_i|`
elements, `A_i` is not regular (so not abelian), and the procedure reports that
orbit as outside item 5. Commutativity is checked on the multiplication table.
Cyclicity is checked by computing the order of each of the `<= k` elements.

**Corollary T.** The `U_i` have the same weighted graph as `U`, so they lie in
the host class. If `val(U) >= c`, step 4 gives some `i` with
`val(U_i) >= c/t >= c/k`. The algorithm, run with completeness parameter `c/k`
on each `U_i` (via step 5, alphabet `Z_(|O_i|)`, `|O_i| <= k`), returns a
labeling of value `>= delta(c/k, |O_i|)` on that `U_i`. Pulling it back through
`phi` and `g`, which step 1 allows, gives a labeling of `U` of at least that
value. Take the best over `i`.

**Corollary BM.** Apply Corollary T with the Bafna--Minzer Theorems 1.6, 1.7 and
1.8 as the host algorithm. The running time `n^D`, with
`D = l^(poly(|Sigma| l^(1/c)))`, is polynomial for fixed `l`, `k` and `c`,
since `|Sigma| <= k`.

**Machine check.** `check_holonomy_reduction.py` builds disguised shift games,
applying a random `h_v in S_k` to each vertex of an `A`-shift game where `A` has
one or two regular orbits. It recomputes items 1, 2, 4 and 5 by brute-force
values: the gauge preserves the value, the gauged constraints lie in `Mon_r`,
the abelian orbit images are regular, the shift form has equal value, and the
orbit sandwich holds.
