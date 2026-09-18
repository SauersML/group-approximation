---
rg: 2
id: sticky-cylinder-gadget-compositions-cannot-prove-sseh
kind: claim
title: A gadget composition over an outer chain with c-sticky cylinders at every scale outputs graphs with Phi(delta) <= 1-c, so bounded-arity label-cover compositions cannot prove SSEH for eta below k^-s
distinct_from:
  small-set-expansion-hypothesis: that is the open hardness statement; this is a precise obstruction on one class of proofs of it, and neither proves nor refutes it.
  small-set-expansion-hypothesis-implies-ugc: that is the published SSE-to-UG reduction; this concerns reductions into SSE, where the graph itself must expand in the NO case.
  entanglement-sound-soundness-cannot-prove-ugc: that kills UG soundness analyses by the strategy class they bound; this kills SSE reductions by a combinatorial invariant of the output graph (sticky cylinders), whatever the soundness analysis.
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that collapses affine-view unique verifiers to quotient games; this is about the expansion profile of the output graph, not the value of any game.
  affine-ug-easy-on-globally-hypercontractive-graphs: that is an algorithm for UG on structured non-expanders; this shows output graphs of gadget compositions over bounded-arity outer games are non-expanders at every scale, with no algorithm needed.
artifacts:
  - experiments/fibred-sse-kill-2026-09-17/check_fibred_kill.py
---

**ESTABLISHED.** Elementary and self-contained. Proof:
`sticky-cylinder-gadget-compositions-kill-proof`.

*Chains.* A finite reversible Markov chain `(V, O, mu)` is given by a symmetric
edge measure `E_O(u,v) = mu(u) O(u,v)`. For `S <= V`,
`Phi_O(S) = E_O(S, V \ S) / mu(S)`. A graph is the chain of its random walk. A
set `A` is **c-sticky** if `O(v, A) >= c` for every `v in A`.

*Gadget compositions (fibrations).* A chain `G'` on `V'` is **fibred** over `O`
through `pi : V' -> V` if `(pi x pi)_* E_(G') = E_O`. Every reduction that
"replaces every vertex of the outer instance by a gadget" and draws each output
edge by drawing an outer step and then correlated gadget points has this form.

*Scale ladders.* A **c-sticky ladder with step `varsigma`** is a chain of
c-sticky sets `emptyset = A_0 <= A_1 <= ... <= A_m` with `mu(A_m) = 1` and
`mu(A_(j+1)) - mu(A_j) <= varsigma`.

**Theorem.**

1. *(Pullback.)* If `G'` is fibred over `O` through `pi`, then
   `mu'(pi^-1 A) = mu(A)` and `Phi_(G')(pi^-1 A) = Phi_O(A) <= 1 - c` for every
   c-sticky `A`.
2. *(Profile.)* If `O` has a c-sticky ladder with step `varsigma`, then for every
   `delta in (0, 1 - varsigma]` some `S' <= V'` has
   `mu'(S') in [delta, delta + varsigma]` and `Phi_(G')(S') <= 1 - c`. If `G'`
   is a regular graph and `delta |V'|` is an integer, some `S'` has
   `mu'(S') = delta` exactly and `Phi_(G')(S') <= 1 - c + 2 varsigma' / delta`,
   where `varsigma' = varsigma + 1/|V'|`.
3. *(Bounded-arity outer games have sticky ladders.)* Let `B = (L, R, w)` be a
   weighted bipartite projection game in which each left vertex `u` spreads its
   weight `w_u` over at most `k` neighbours, each edge carrying at least `w_u/k`
   (for example uniformly over `<= k` neighbours). Put
   `varsigma_B = (k+1) max_(x in R) mu(x)`, with `mu` the stationary measure on
   `L u R`. For `X <= R` let `N(X)` be its neighbourhood. Then:
   - the walk `P` on `L u R` and every power `P^t` (odd or even `t`): `X u N(X)`
     is `k^(-ceil(t/2))`-sticky. For `t = 1`, `Phi_P(X u N(X)) <= (k-1)/(k+1)`.
     For even `t = 2s`, `1 - Phi_(P^(2s))(X u N(X)) >= (2/(k+1))^(2s)`;
   - the two-step walk restricted to one side, `P_R = P^2|_R` and
     `P_L = P^2|_L`, and their powers `s`: `X` and `N(X)` are `k^(-s)`-sticky;
   - adding right vertices one at a time gives ladders with step
     `<= varsigma_B` for `P^t` and `P_R^s`, and `<= 2 varsigma_B` for `P_L^s`;
   - the `r`-fold parallel repetition `B^r` (left arity `k^r`): the union
     cylinder `{ubar : some u_i in N(X)} u {xbar : some x_i in X}` is
     `1/k`-sticky with step `<= r varsigma_B`.
4. *(Closure.)* Sticky ladders survive the operations reductions use:
   - lazy or noisy mixtures `a O + (1-a) Q`, where `Q` is any chain on `V` with
     the same `mu`, with constant `a c`. The re-randomising step `Q = mu`
     contributes `(1-a) mu(A)` more;
   - tensoring with any gadget chain `H`: `A x V_H` has constant `c` and step
     `varsigma`;
   - `r`-fold independent products `O^(tensor r)` (parallel repetition). The
     union cylinder `U_A = { vbar : some v_i in A }` has constant `c` and step
     `<= r varsigma`. The coordinate cylinder `{ v_1 in A }` has step
     `varsigma`. The union cylinder descends to the quotient by any group of
     coordinate permutations (folding), because `U_A` is invariant;
   - quotients of `G'` by any group acting on `V'` with `pi o gamma = pi`
     (folding over gadget symmetries) are again fibred over `O`;
   - powers: `O^t` makes every c-sticky set `c^t`-sticky;
   - composition of fibrations.
5. *(Class kill.)* Fix `eta, delta`. Let `R` be a map from instances of a promise
   problem to graphs. Suppose that on some NO instance `x`, `R(x)` is fibred over
   a chain with a c-sticky ladder of step `varsigma(x)` satisfying either
   `eta < c` and `varsigma(x) <= 9 delta` (the `[delta, 10 delta]` convention),
   or `eta + 2 varsigma'(x)/delta < c` (regular graphs, exact volume). Then
   `R(x)` is not a NO instance of `Gap-SSE(eta, delta)`, so `R` is not a
   reduction to it. No complexity assumption is used.

**What dies, and where.** Consider proofs of `small-set-expansion-hypothesis` by
composing an outer label-cover-type game with local gadgets (long code, short
code, noisy cube, Grassmann or any dictatorship-test graph attached to each outer
vertex). Every such proof dies at the **NO case of the output graph**, before any
soundness analysis is reached, whenever the outer chain is built by powers `<= t`,
mixtures, gadget tensoring, parallel repetition and folding from a projection game
of left arity `<= k` with `k^(-ceil(t/2)) > eta` (or `k^(-s) > eta` for one-sided
`s`-step walks), once `varsigma` is small against `delta`. The invariant is the
**stickiness constant of arity cylinders**. It depends only on `(k, t)` and the
laziness `a` of any mixture, and it ignores source soundness, alphabet,
repetition count and gadget.

So for SSEH, which quantifies over all `eta > 0`, a composition family must have
outer arity `k(eta) >= eta^(-1/ceil(t/2))`, or unbounded walk length, or break the
fibration. Every fixed-arity PCP outer game (3-LIN, 3-SAT, any `q`-query PCP with
`q` fixed, smooth label cover obtained by parallel repetition, the 2-to-2 outer
games) fails for all `eta < k^(-ceil(t/2))`. The KMS remark that 2-to-2 graphs
"always have small non-expanding sets" (see Attempts of
`small-set-expansion-hypothesis`) is one instance of this phenomenon.

**The gate.** Raghavendra--Steurer--Tulsiani (arXiv:1011.2586v1, p. 3) write that
"Gadget reductions from a unique games instance preserve the global properties of
the unique games instance such as lack of expansion". On p. 9 they say their
modified reduction "will break with the paradigm of composing unique games with
local gadgets", and on p. 10 that `H` "had the same structure as `G^(tensor R)`"
while `H'` does not. Item 5 makes the first sentence a theorem with explicit
constants.

The survivors are exactly:

- **(G1)** outer chains without sticky cylinders at scale `delta`, which must
  themselves be near-perfect small-set expanders in this pointwise sense. The RST
  gate is of this kind: its outer input is an SSE graph `G`, so it consumes SSE
  hardness and cannot start it;
- **(G2)** non-fibred output graphs, whose edges are not drawn along outer steps;
- **(G3)** outer arity growing like `eta^(-1/ceil(t/2))`.

The replay script checks items 3, 4 (products, noise, tensoring) and the pullback
numerically. The bounds are attained.

DERIVATION sticky-cylinder-gadget-compositions-kill-proof
