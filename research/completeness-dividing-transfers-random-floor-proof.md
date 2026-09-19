---
rg: 2
id: completeness-dividing-transfers-random-floor-proof
kind: route
title: Conditional expectations give the 1/k floor; Hoeffding plus a union bound over labelings plants shift games at any completeness on high-degree hosts; comparing the two bounds the orbit-split and coset-lift certificates; pushing labels through equivariant orbit maps gives the dominated split
target: completeness-dividing-host-transfers-never-beat-random-labeling
requires:
  - unique-games-reduce-to-shifts-over-their-holonomy-group
  - affine-ug-easy-on-globally-hypercontractive-graphs
artifacts:
  - experiments/ugc-random-floor-2026-09-17/check_random_floor.py
  - experiments/ugc-random-floor-2026-09-17/output.txt
---

A direct proof. It uses items 2 and 4 (tree gauge, orbit split) of
`unique-games-reduce-to-shifts-over-their-holonomy-group`, and, only for the
quantifiers in items 3, 5 and 6, Bafna--Minzer (arXiv:2304.07284) through
`affine-ug-easy-on-globally-hypercontractive-graphs`. Theorem 1.7, verbatim:
"For all c > 0 there exists δ > 0 such that the following holds. There exists
an algorithm whose running time is n^D with D = ℓpoly(|Σ|ℓ^{1/c}) which on
input Ψ, an affine UG instance over Grass(n, ℓ) promised to be at least
c-satisfiable, finds an assignment that satisfies at least δ-fraction of the
constraints in Ψ." Here `delta` depends only on `c`. The text adds: "We prove
that Algorithm 3.4 returns a solution with value independent of the alphabet
size." Theorem 1.6 is the same statement for `J(n, l, alpha l)`, with `delta`
depending on `alpha` and `c`.

**Host facts.** In `Grass(n, l)`, a neighbour `L'` of `L` is fixed by a
hyperplane `M` of `L` (`2^l - 1` choices) and an `l`-space `L' ⊃ M` other than
`L`. These are the lines of `F_2^n / M` other than `L / M`, so there are
`2^(n-l+1) - 2` of them. Hence `d = (2^l - 1)(2^(n-l+1) - 2)`. For
`J(n, l, alpha l)`, `d = C(l, alpha l) C(n - l, l - alpha l)`. Both graphs are
vertex-transitive, hence regular. Both are loop-free (`dim(L cap L) = l`, and
`alpha l < l`), and `d -> infinity` as `n -> infinity`.

**1. Random floor.** Label the vertices `v_1, ..., v_N` one at a time. Let
`Phi` be the expected satisfied weight when the unset vertices get independent
uniform labels. An edge `(u, v)`, `u != v`, with at least one unset endpoint is
satisfied with probability exactly `1/k`, because `pi_e` is a bijection. So
initially `Phi = w(E)/k`. Since `Phi` is the average over `x in [k]` of its
value after setting `v_i = x`, some `x` does not decrease it. Each `Phi` is a
sum of `|E|` explicit terms. After `N` steps `Phi` is the value of the
labeling, and it is `>= w(E)/k`. Applied to the root claim: the trivial
algorithm has guarantee `1/k` at every `c`. For R1--R4 and Corollary BM, which
are the same statement on subclasses, it also has guarantee `1/k`.

**2. Planted ceiling.** Fix `sigma* in A^V` and `p = c' + eps`, capped at `1`
(if `c' + eps >= 1`, the plain all-planted instance, of value `1`, already
satisfies the bound). Independently for each edge `e = (u, v)`: with
probability `p`, set `b_e = sigma*_v sigma*_u^(-1)` ("planted"); otherwise draw
`b_e` uniform in `A`. Fix a labeling `x in A^V`. Its edge indicators
`1[x_v = b_e x_u]` are independent. Each has mean
`p 1[x_v x_u^(-1) = sigma*_v sigma*_u^(-1)] + (1 - p)/K <= p + (1 - p)/K`.
With `|E| = N d / 2`, Hoeffding gives
`Pr[sat(x)/|E| >= p + (1-p)/K + eps] <= exp(-2 eps^2 |E|) = exp(-eps^2 N d)`.
A union bound over the `K^N` labelings gives failure probability at most
`exp(N (ln K - eps^2 d)) <= e^(-N)`. The planted fraction is `< p - eps` with
probability at most `exp(-eps^2 N d) <= e^(-N)`, and `sigma*` satisfies every
planted edge. Since `2 e^(-N) < 1` for `N >= 1`, some instance has
`c' = p - eps <= val <= p + (1 - p)/K + eps <= c' + (1 - c')/K + 2 eps`.
For `c' = 0`, take `p = 0`. Then there is no planted edge, and the same bound
gives `val <= 1/K + eps`.

A guarantee `delta(c')` must hold for every `n`. For every `eps`, the hosts
with large `n` satisfy `eps^2 d >= ln K + 1`, and they carry an instance of
value in `[c', c' + (1 - c')/K + 2 eps]`. So
`delta(c') <= c' + (1 - c')/K`. If `delta` does not depend on the group, let
`K -> infinity` over `A = Z_K`. This gives `delta(c') <= c'`.

**3. Orbit split.** Corollary T runs the `Z_q` algorithm on each `U_i` and
certifies `min_(q <= k) delta(c/k, q)`. The minimum is over all `q <= k`,
because an orbit of any size up to `k` can occur. The `c' = 0` instance of
item 2 over `Z_k` is itself a unique game with cyclic (regular) holonomy on a
single orbit. By item 1 its value is `>= 1/k >= c/k`, and it is `<= 1/k + eps`.
So `delta(c/k, k) <= 1/k + eps` for every `eps`. The same instance bounds
`delta_BM(c/k) <= 1/k`, since `delta_BM` does not depend on `q`. For the class
kill, its NO case asks for instances of value `< delta(c/k) <= 1/k`. By item 1
no unique game with alphabet `k` on a loop-free host has such value, so the
kill excludes nothing.

**4. Coset lift.** *Upper bound.* If `x_v = pi_e x_u`, then
`x_v(0) = pi_e(x_u(0))`. So the projection `sigma_v = x_v(0)` satisfies every
edge that `x` satisfies. *Lower bound.* Given `sigma`, draw `x_v` uniform and
independent in the coset `C_v = {g in S_k : g(0) = sigma_v}`, of size
`(k-1)!`. On an edge satisfied by `sigma`, `pi_e x_u` is uniform on
`pi_e C_u = C_v` and independent of `x_v`. So it equals `x_v` with probability
`1/(k-1)!`, and some `x` reaches `val(U)/(k-1)!`. A transfer through the lift
knows only `val(L(U)) >= c/(k-1)!`. So it certifies
`delta_(S_k)(c/(k-1)!)`, which item 2 (with `A = S_k`, `K = k!`) bounds by
`c/(k-1)! + 1/k!`. Then `c/(k-1)! + 1/k! < 1/k` iff `c k + 1 < (k-1)!`. For
`c <= 1` this holds at `k = 4` (`5 < 6`) and at every larger `k`.
*Genuine loss.* On the planted instances, fix `x`. On a planted edge,
`1[x_v = pi_e x_u] = 1[pi_e = x_v x_u^(-1)]`. This has probability
`1/(k-1)!` if `x_v x_u^(-1)(sigma*_u) = sigma*_v`, and `0` otherwise. On the
other edges it has probability `1/k!`. So the mean is at most
`p/(k-1)! + (1-p)/k!`. Hoeffding and a union bound over `(k!)^N` labelings, as
in item 2, give `val(L(U)) <= p/(k-1)! + 1/k! + eps` whenever
`eps^2 d >= ln k! + 1`. Meanwhile `val(U) >= p - eps`.

**5. Unbounded losses.** Item 2 bounds a `k`-independent guarantee `delta` by
`delta(c/L(k)) <= c/L(k)`, and this tends to `0` as `L(k) -> infinity`.

**6. Dominated split.** Work in the tree gauge, where every constraint lies in
`H` and preserves each orbit.

* *Maps.* An `H`-equivariant `rho : O_i -> O_j` sends `o` with stabilizer `S`
  to `rho(o)`, whose stabilizer contains `S`. Conversely, if
  `S_i <= g S_j g^(-1) = Stab(g o_j)`, then `h o_i -> h g o_j` is well defined
  and equivariant.
* *Upper bound.* Fix `D` dominating and maps `rho_i : O_i -> O_(j(i))`,
  `j(i) in D`. For an optimal `sigma` of `U`, let `V_j` be the set of vertices
  whose label lies in some `O_i` with `j(i) = j`. Define `sigma^(j)` by
  `rho_i(sigma_v)` on `V_j`, and arbitrarily in `O_j` elsewhere. A satisfied
  edge has both labels in one orbit `O_i`, since constraints preserve orbits.
  Also `rho_i(pi_e sigma_u) = pi_e rho_i(sigma_u)`. So that edge is satisfied
  by `sigma^(j(i))` in `U_(j(i))`. Summing over `j in D` gives
  `val(U) <= sum_(j in D) val(U_j)`.
* *Lower bound.* This is item 4 of the holonomy node.
* *Cyclic case.* A cyclic `H` has one subgroup of each index dividing `|H|`,
  and conjugation is trivial. So `O_i -> O_j` exists iff `|O_j|` divides
  `|O_i|`.
* *Algorithm.* If `val(U) >= c`, some `j in D` has `val(U_j) >= c/tau`.
  Running Bafna--Minzer on every `U_j` (these are `Z_(|O_j|)`-shift games on the
  same host by item 5 of the holonomy node) and keeping the best labeling gives
  value `>= delta_BM(c/tau)`.
* *Fixed point.* A fixed point is an orbit of size `1`, whose single label
  satisfies every gauged constraint.
