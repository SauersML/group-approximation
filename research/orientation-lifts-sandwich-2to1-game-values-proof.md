---
rg: 2
id: orientation-lifts-sandwich-2to1-game-values-proof
kind: route
title: Project the right bit away, randomize it back, and read the canonical orientation off the sigma-fibres
target: orientation-lifts-sandwich-2to1-game-values
requires: [sd-rich-and-unique-games-sos-gaps-interconvert, rich-2to1-conjecture-is-equivalent-to-ugc]
---

Edge weights `w_e` sum to 1 throughout.

**(1) Upper bound.** Let `(L, M)` label `U_o`, with `M_v = (m_v, c_v)`. If an edge
`e = (u,v)` is satisfied in `U_o`, then `(p_e(L_u), o_e(L_u)) = (m_v, c_v)`, so
`p_e(L_u) = m_v`. Hence `(L, m)` satisfies `e` in `G`, and
`val_(U_o)(L,M) <= val_G(L,m)`.

**(1) Lower bound.** Let `(L, m)` label `G`. Draw independent uniform bits `c_v`
and put `M_v = (m_v, c_v)`. An edge satisfied in `G` is satisfied in `U_o` iff
`c_v = o_e(L_u)`, which has probability `1/2`. Unsatisfied edges stay
unsatisfied. So `E val_(U_o)(L, M) = val_G(L,m)/2`, and some choice of bits
attains it.

**(1) Tightness.** Upper: if `o_e` agrees at every right vertex on the labels in
an optimal labelling (for example a single edge), then `val(U_o) = val(G)`.
Lower: take `k = 1`, one left vertex `u`, one right vertex `v`, and two parallel
edges of weight `1/2` with `o_(e1)(a) = a` and `o_(e2)(a) = 1 - a`. Then
`val(G) = 1`, and every right bit disagrees with one of the two edges, so
`val(U_o) = 1/2`.

**(2)** `U_o` is a bipartite unique game with alphabet `[2k]`, since each
`a -> (p_e(a), o_e(a))` is injective between sets of size `2k`. Item (a) of
`sd-rich-and-unique-games-sos-gaps-interconvert` gives full richness of
`Psi(U_o)` and `val(U_o) <= val(Psi(U_o)) <= 2 val(U_o)`. That proof works with
weighted neighbour laws. Chain with (1).

**(3)** Fix `L`. At a right vertex `v`, the right label `(m, b)` gains exactly the
weight of edges with `p_e(L_u) = m` and `o_e(L_u) = b`. Maximizing over `(m, b)`
and then over `L` gives the formula, where `w_v(L, b)` uses the best `m` for the
branch. (Maximizing `m` inside `b` is the same as outside, since both maxima are
over pairs.)

**(4)** Fix a labelling `L` of `U` with right labels `M_v`. At the right vertex
`(v, sigma)` of `Psi(U)`, put the lift label `(sigma(M_v), t)`, where `t = 1` iff
`M_v` is the larger element of its `sigma`-fibre. The lifted constraint on the
edge `(u, (v,sigma))` sends `a` to
`(sigma(phi_(uv)(a)), [phi_(uv)(a) is the larger element of its fibre])`. The map
`x -> (sigma(x), [x is larger in its fibre])` is a bijection of `[2k]`. So the
lifted edge is satisfied iff `phi_(uv)(L_u) = M_v`, that is, iff `(u,v)` is
satisfied in `U`. Every right vertex `(v, sigma)` spreads `v`'s weight over
`sigma`, so `val(U_canonical) >= val_U(L, M)`.

**(5)** `o_e(s) xor lambda_e(s)` takes the same value on `s` and `s + chi_e`: both
terms flip, `o_e` by injectivity on the fibre and `lambda_e` because
`lambda_e(chi_e) = 1`. So it is a function `g_e` of the fibre `p_e(s)`, and it is
unique given `lambda_e`. In the restriction case, `chi_e` is the functional on `L`
vanishing on `L'`, so `chi_e(x_e) = 1` for `x_e in L \ L'`, and
`lambda_e(s) = s(x_e)` qualifies. An affine offset `p_e(s) = s|_(L') + h` changes
`g_e` by a translation of its argument.

**Consequence (a).** Compose `R`, `U_o` and `Psi`. All are polynomial, because `o`
is and `k` is a constant. YES: `val(Psi(U_o)) >= val(U_o) >= c`. NO:
`val(Psi(U_o)) <= 2 val(U_o) <= 2 val(G) <= 2s`, and `val(U_o) <= s`. With the
random-bit bound of (1), `c = (1 - eta)/2` holds for every orientation.

**Consequence (b).** "If" is (a) applied at every `eps`. For "only if", apply
`rich-2to1-conjecture-is-equivalent-to-ugc` to get UG hardness at `eps/2`. Pad the
alphabet by `phi x id`, which preserves the value both ways: extend labels by the
bit 0, and project. Then apply (4) and (2) to the composite.

**Regression replay.** `experiments/orientation-lift-2026-09-17/check_orientation_lift.py`
replays (1), (2), (4) and (5) with exact rationals. It checks 160 random lifts of
weighted games with `k = 2`, 30 unique games, and 50 linear maps `F_2^3 -> F_2^2`,
with 0 failures. This is a regression check; the proof above does not depend on
it. `square`
