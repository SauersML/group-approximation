---
rg: 2
id: spread-support-overlap-forces-non-expanding-small-sets
kind: claim
title: If a graph carries a support map whose neighbours share a theta fraction of their supports and no atom lies in more than a rho fraction of vertices, some set of measure in [delta, 10 delta] has Phi <= 1 - theta + rho/delta, so Grassmann, agreement-test and bounded-query view graphs cannot be NO outputs of an SSEH reduction for eta below theta
distinct_from:
  sticky-cylinder-gadget-compositions-cannot-prove-sseh: that kills fibred compositions over bounded-arity outer chains through a deterministic ladder of arity cylinders; this needs no outer chain and no fibration, only a spread support map on the output graph, finds the set by a p-biased random zoom plus Efron--Stein, and also kills arbitrary-arity Grassmann and agreement-test graphs, which that claim lists as survivors (G2), (G3).
  small-set-expansion-hypothesis: that is the open hardness statement; this is an obstruction on the NO outputs of any reduction proving it, and neither proves nor refutes it.
  low-label-threshold-rank-reductions-cannot-prove-ugc: that kills UG reductions at the YES case by a spectral invariant; this kills SSE reductions at the NO case by a combinatorial support-overlap invariant.
  grassmann-composed-2to2-coarsenings-are-satisfiable: that shows agreement games on the folded Grassmann vertex set are satisfiable; this shows every graph on Grassmann views with codimension-one adjacency has non-expanding sets at every scale above 2^(l-n)/delta.
  two-to-two-games-theorem: that is the KMS hardness theorem; this only uses the codimension-one Grassmann adjacency of its test as one instance of the overlap invariant.
artifacts:
  - experiments/support-overlap-sse-kill-2026-09-17/check_support_overlap_kill.py
---

**ESTABLISHED.** Elementary and self-contained. Proof:
`spread-support-overlap-kill-proof`.

*Setting.* A finite weighted graph (reversible chain) on `V` is a symmetric edge
measure `E` on `V x V` with marginal `mu`. For `S <= V`,
`Phi(S) = E(S, V \ S) / mu(S)`, so `1 - Phi(S) = E(S, S) / mu(S)`. A regular
graph has `mu` uniform and `E` uniform on ordered edges.

*Support maps.* A **support map** is a map `psi : V -> 2^U` into subsets of a
finite set `U` (views, queried positions, subspace points). Put
`b(v) = |psi(v)|`, `a(v, v') = |psi(v) n psi(v')|`, and
`g_p(s) = 1 - (1 - p)^s`. Define:

- the **spread** `rho(psi) = max_(x in U) mu{ v : x in psi(v) }`;
- the **coverage** `mu(psi) = mu{ v : psi(v) != emptyset }`;
- `psi` has **overlap `theta`** if for every `p in (0, 1)`
  `E_((v,v') ~ E) g_p(a(v, v')) >= theta E_(v ~ mu) g_p(b(v))`.

**Pointwise overlap** `a(v, v') >= theta b(v)` on every edge implies overlap
`theta`. So does the one-sided version in which, from every `v`, edges of
conditional mass `>= 1 - beta` satisfy it, with `theta (1 - beta)`.

*Zoom sets.* For `X <= U` put `Z_X = { v : psi(v) n X != emptyset }`.

**Theorem.**

1. *(Zoom inequality.)* Let `X` be `p`-biased random in `U`, and put
   `B_X = mu(Z_X)` and `A_X = E(Z_X, Z_X)`. If `psi` has overlap `theta`, then
   `E A_X >= theta E B_X`, and `m(p) := E B_X = E_mu g_p(b)`. Also
   `Var B_X <= rho(psi) m(p)`.
2. *(Scale.)* Suppose `psi` has overlap `theta` and `rho(psi) <= delta`, and
   `3 delta <= mu(psi)`. Then some `X <= U` has
   `mu(Z_X) in [delta, 10 delta]` and
   `1 - Phi(Z_X) >= theta - rho(psi) / delta`.
3. *(Exact volume.)* If moreover the graph is regular on `n` vertices and
   `s = delta n` is an integer `>= 2`, then some `T` with `|T| = s` has
   `1 - Phi(T) >= (theta - rho/delta)(s - 1)/(10 s)`.
4. *(Closure.)* Overlap and spread survive the operations reductions use:
   - *gadget tensoring* `E tensor E_H`, with `psi(v, h) = psi(v)`;
   - *fibred pullback* `(pi x pi)_* E' = E`, with `psi' = psi o pi`;
   - *mixtures* `alpha E + (1 - alpha) E_Q` with any `Q` of the same marginal,
     with overlap `alpha theta`;
   - *parallel repetition* `E^(tensor r)` with the disjoint-union support
     `psi(vbar) = u_i {i} x psi(v_i)`, for pointwise overlap `theta`, with the same
     spread;
   - *folding* by a group preserving `E` and `psi`.
5. *(Instances.)*
   - **Grassmann views.** Take any graph on `V = Gr_l(F_q^n) x Lab`, with any
     labels, whose edges join `(L, f)` to `(L', f')` with
     `dim(L n L') >= l - 1`. The map `psi(L, f) = L \ {0}` has pointwise overlap
     `(q^(l-1) - 1)/(q^l - 1)` (at least `1/2 - 2^(-l)` for `q = 2`) and spread
     `(q^l - 1)/(q^n - 1)` when the marginal of `mu` on subspaces is uniform.
   - **Agreement tests.** Take `k`-sets of `[N]` joined when they meet in at
     least `theta k` points, with `psi` the set itself: overlap `theta`, spread
     the maximal fraction of vertices containing a point.
   - **Bounded-query view graphs.** Vertices are local views of a `q`-query
     verifier, and edges join views that share a queried position:
     `psi` = the queried positions, with overlap `>= 1/q` and spread the
     maximal read-frequency of a position (small for smooth verifiers).
   - **Projection games of left arity `k`.** For the walk on `L u R` of a
     bipartite projection game in which each left vertex `u` has at most `k`
     neighbours, each edge at `u` carrying at least `w_u/k`: with
     `psi(u) = N(u)` and `psi(x) = {x}`, pointwise overlap is `1/k` and spread
     is at most `(k + 1) max_x mu(x)`. This recovers the `t = 1` case of
     `sticky-cylinder-gadget-compositions-cannot-prove-sseh` up to constants.
6. *(Class kill.)* Fix `eta, delta`. Let `R` map instances of a promise problem
   to graphs. Suppose some NO instance `x` has `R(x)` carrying a support map with
   overlap `theta`, coverage `>= 3 delta`, and `eta < theta - rho/delta`
   (for the `[delta, 10 delta]` convention), or
   `eta < (theta - rho/delta)(s - 1)/(10 s)` (regular graphs, exact volume
   `s = delta n`). Then `R(x)` is not a NO instance of `Gap-SSE(eta, delta)`,
   so `R` is not a reduction to it. No complexity assumption is used.

**What dies, and where.** A proof of `small-set-expansion-hypothesis` must, for
every `eta > 0`, output graphs whose NO instances have `1 - Phi(S) <= eta` for
all `S` of measure in `[delta, 10 delta]`. It dies at the **NO case of the output
graph**, before any soundness analysis, as soon as the output graph carries one
spread support map (`rho <= delta (theta - eta)`) with overlap `theta > eta`.

- *The invariant* is the **spread overlap profile**
  `Theta_G(delta) = sup_psi ( theta(psi) - rho(psi)/delta )`, over support maps
  with coverage `>= 3 delta`. Item 2 says `1 - Phi_G([delta, 10 delta]) >= Theta_G(delta)`.
- *The step* is the p-biased zoom set `Z_X` at `m(p) = 3 delta`. Neighbouring
  views that share a `theta` fraction of atoms meet a random atom set together
  with probability at least `theta` times the one-sided probability. This is the
  concavity of `g_p`. Efron--Stein with spread `rho` pins `mu(Z_X)` to the scale.

Consequences:

- **Grassmann-type outputs die at every arity.** Every graph built on
  `Gr_l(F_2^n)` views with codimension-one adjacency (the 2-to-2 test adjacency,
  with any labels, fibres or tensored gadgets) has
  `1 - Phi([delta, 10 delta]) >= 1/2 - 2^(-l) - 2^(l-n+1)/delta`. So it is never
  a NO instance of `Gap-SSE(eta, delta)` for `eta < 0.49` once `l >= 8`,
  `delta <= 1/3` and `n >= l + 9 + log_2(1/delta)`. Over `F_q` the threshold is about `1/q`. This makes the
  KMS remark (ECCC TR18-006, App. B) that 2-to-2 graphs "always have small
  non-expanding sets" a theorem with explicit constants. Unlike the sticky-cylinder kill, it does
  not depend on outer arity: survivor (G3) of that claim with `F_2` Grassmann
  views is dead for all `eta < 0.49`.
- **Agreement-test and direct-product outputs** with intersection fraction
  `theta` die for `eta < theta - rho/delta`. So an SSEH reduction by agreement
  testing needs intersection fraction `theta(eta) <= eta + o(1)`.
- **Bounded-query view graphs** (views of a smooth `q`-query verifier, adjacent
  when they share a position) die for `eta < 1/q - rho/delta`, whatever the
  alphabet, soundness or gadget. This includes non-fibred graphs, survivor (G2)
  of the sticky-cylinder kill, whenever edges join views sharing positions.

**Survivors.** Exactly the graphs where every support map with overlap
`theta > eta` and coverage `>= 3 delta` is **concentrated**: some atom lies in
at least a `delta (theta - eta)` fraction of vertices.

- **(H1) Dense-atom graphs.** Examples are the noisy hypercube and long-code
  gadgets. The map `psi(x) = {(i, x_i)}` has overlap `1 - eps`, but spread `1/2`.
  This is the calibration: its zoom sets are dictator halves, and the noisy cube
  is a genuine small-set expander.
- **(H2) Vanishing-overlap graphs.** In these, neighbours share at most an
  `eta + rho/delta` fraction of every spread support. Examples are sparse-intersection
  agreement tests with `theta(eta) -> 0`, or random-like
  graphs with no view structure.

A reduction proving SSEH therefore needs outputs whose local structure is
either carried by dense atoms (H1) or whose adjacency almost forgets the view
(H2). (Support maps with coverage below `3 delta` are also not covered.) Which
type the RST graph `H'` belongs to was not checked here.

The replay script checks the zoom inequality exactly, and the Efron--Stein
variance bound by exact variance computation. It runs the scale search and the
downsampling identity on Grassmann `G_2(6,3)` and Johnson `J(24,3)`.

DERIVATION spread-support-overlap-kill-proof
