---
rg: 2
id: fpbs-expander-approximant-giant-data-is-glued-proof
kind: route
title: Sandwich finite connections between local connections and giant membership
target: fpbs-expander-approximant-giant-data-is-glued
requires:
  - fpbs-msf-excess-equals-nonuniqueness
artifacts:
  - experiments/expander-glued-giant-2026-09-17/rrg_glued_calibration.py
---

Complete written proof. It imports one published theorem verbatim (ABS
Theorem 1.1) and uses the Lyons--Peres--Schramm forest facts recorded in
`fpbs-msf-excess-equals-nonuniqueness`. Everything else is proved here.

## Setting and imported theorem

`G = Cay(Gamma,S)` is a nonamenable Cayley graph, which is transitive and
unimodular. The graphs `G_n` are finite, possibly random, simple, with `n`
vertices and maximum degree at most `D`. `B_R(v)` is the graph ball, and
`M_r = (D+1)^r` bounds `|B_r(v)|`. The expectation `E_n` averages over the
graph, the percolation `omega` and a uniform vertex `o_n`.

Local convergence in probability to the deterministic graph `G` means: for
every `R`, the fraction of vertices `v` of `G_n` whose rooted ball `B_R(v)` is
isomorphic to `B_R(o)` in `G` tends to `1` in probability.

**Fact L (local functions).** Let `F(v)` be a function of the rooted ball
`B_{R'}(v)` and of `omega` restricted to its edges, invariant under rooted
isomorphism and bounded by `M`. Then `E_n F(o_n) -> E_G F(o)`. *Proof:*
`E_n F(o_n)` is the expectation of `(1/n) sum_v E_omega F(v)`. For good `v`,
`E_omega F(v) = E_G F(o)`. The bad fraction tends to `0` in probability, so it
tends to `0` in expectation, and it contributes at most `M` times itself.

**Imported theorem (ABS).** Y. Alimohammadi, C. Borgs, A. Saberi, *Locality of
random digraphs on expanders*, arXiv:2103.09952v3, Theorem 1.1, verbatim
(transcribed from the arXiv PDF):

> "Let {G_n} be a sequence of (possibly random) large-set expanders with
> bounded average degree converging locally in probability to (G,o) ∈ G* with
> non-random distribution μ. Let C_i be the ith largest component of G_n(p).
> If p ≠ p_c(μ), then |C_1|/n →P ζ(p), with →P denoting convergence in
> probability with respect to both μ and percolation. Moreover, for all
> p ∈ [0,1], |C_2|/n →P 0, where the convergence is uniform on any closed
> interval I ⊂ (0,1) ..."

Here `zeta(p) = E_mu[P(|C(o)| = infinity)]` and
`p_c(mu) = inf{p : zeta(p) > 0}`. For `mu` the point mass at `G`, these are
`zeta(p) = P_G(|C(o)| = infinity)` and `p_c(mu) = p_c(G)`. A large-set expander
sequence is one with average degree at most some `dbar` such that, for every
`alpha in (0,1/2)`, with probability tending to `1` every vertex set `A` with
`alpha n <= |A| <= n/2` has at least `beta |A|` boundary edges, for some fixed
`beta > 0`.

**Part (A)** is the second assertion of the theorem.

## Part (B): the sandwich

Fix `p != p_c(G)` and `r`. For `R > r` and `y in B_r(x)`, let `L_R` be the event
that `x` and `y` are joined by an open path inside `B_R(x)`. Let
`A_K(v) = {|C(v)| >= K}`. An exploration finds the first `K` cluster vertices
within distance `K - 1`, so `A_K(v)` depends only on edges in `B_K(v)`.

*Step 1: the tail estimate.* Put
`eps_K = P_G(|C(o)| >= K) - zeta(p)`, which tends to `0` as `K -> infinity`.
Then

`P_n(A_K(o_n), o_n not in C_1) = P_n(A_K(o_n)) - P_n(o_n in C_1) + P_n(o_n in C_1, |C_1| < K)`.

The first term tends to `P_G(|C| >= K)` by Fact L. The second is
`E_n |C_1|/n`, which tends to `zeta(p)` by ABS and bounded convergence. The
third is at most `K/n`. Hence `limsup_n P_n(A_K(o_n), o_n not in C_1) <= eps_K`.

*Step 2: mass transport on the finite graph.* For any function `g` of
`(G_n, omega, v)` with values in `[0,1]`,

`E_n sum_{y in B_r(o_n)} g(y) = E (1/n) sum_y |B_r(y)| g(y) <= M_r E_n g(o_n)`.

*Step 3: event inclusions.* If `x <-> y` but `L_R` fails, the open path leaves
`B_R(x)`. It therefore visits at least `R + 2` vertices, so `A_R(x)` holds.
Either `x in C_1`, and then `y in C_1` too, or `x` is not in `C_1`. Also, if
`x, y in C_1`, then `x <-> y`. So

`1{L_R} + 1{x,y in C_1, not L_R} <= 1{x <-> y} <= 1{L_R} + 1{x,y in C_1, not L_R} + 1{A_R(x), x not in C_1}`.

Next compare `{x, y in C_1}` with `{A_K(x), A_K(y)}`. The first event is
contained in the second together with `{x in C_1, |C_1| < K}` and the same
event for `y`. The second event is contained in the first together with
`{A_K(x), x not in C_1}` and `{A_K(y), y not in C_1}`.

*Step 4: limit in `n`.* Let
`Phi_n = E_n sum_{y in B_r(o_n)} 1{o_n <-> y}`. Let
`F_{R,K}(x) = sum_{y in B_r(x)} [1{L_R} + 1{A_K(x), A_K(y), not L_R}]`. This is
a local function of radius `R + K + r`, bounded by `2 M_r`. Steps 1--3 and
Fact L give, for all `R > r` and all `K`,

`E_G F_{R,K}(o) - 2 M_r eps_K <= liminf_n Phi_n <= limsup_n Phi_n <= E_G F_{R,K}(o) + 2 M_r eps_K + M_r eps_R`.

The `K/n` terms vanish.

*Step 5: remove the scales.* As `K -> infinity`, `A_K(v)` decreases to
`{|C(v)| = infinity}`. By monotone convergence `E_G F_{R,K}` tends to
`sum_y [P_G(L_R) + P_G(|C(o)| = |C(y)| = infinity, not L_R)]`. As
`R -> infinity`, `L_R` increases to `{o <-> y}`, so this quantity tends to
`sum_y [P_G(o <-> y) + P_G(both infinite, o not connected to y)]`, which
equals `sum_y P_G(o <-> y or both infinite)`. Also `eps_R -> 0`. Since `Phi_n`
does not depend on `R` or `K`, the liminf and limsup coincide with this value.
This proves (B).

## Part (D): the two-scale defect

Fix an edge slot `e = o_n y` at the root and include the local indicator
`1{omega(e) = 0}` in every event above. Steps 1--4 go through verbatim with
`r = 1`. Let `F'_{R,K}(x) = sum_{y ~ x} 1{e closed, A_K(x), A_K(y), not L_R}`.
The steps give

`E_G F'_{R,K} - 2 M_1 eps_K <= liminf_n s_n(p,R) <= limsup_n s_n(p,R) <= E_G F'_{R,K} + 2 M_1 eps_K + M_1 eps_R`.

The lower bound uses `{e closed, x, y in C_1, not L_R} ⊂ {e closed, x <-> y, not L_R}`.
The upper bound uses the right-hand inclusion of Step 3.

Let `K -> infinity`. Then `E_G F'_{R,K}` tends to
`Psi(R) = sum_{y ~ o} P_G(e closed, both infinite, not L_R)`, and
`|limsup_n s_n(p,R) - Psi(R)| <= M_1 eps_R`, and likewise for the liminf. As
`R -> infinity`, `Psi(R)` decreases to
`sum_{y ~ o} P_G(e closed, |C(o)| = |C(y)| = infinity, o not connected to y)`.
On `{e closed}` we have `omega = omega \ e`, and `omega \ e` is independent of
`omega(e)`. So the limit is `(1-p) Delta(p)`, where
`Delta(p) = sum_{e ∋ o} P_G(endpoints in distinct infinite clusters of omega \ e)`.

For finite `n`, `s_n(p,R) = 0` whenever `R >= diam(G_n)`, because then
`L_R` is the same event as `x <-> y`. So the order of limits cannot be
reversed.

*Positivity.* Suppose a unique infinite cluster exists almost surely. With `e`
closed, two endpoints in infinite clusters of `omega` are then connected, so
`Delta(p) = 0`.

Conversely, suppose that with positive probability there are two distinct
infinite clusters. Let `m >= 1` be the least distance between two distinct
infinite clusters, and let `v_0 ... v_m` be a shortest path with `v_0 in C'`
and `v_m in C''`. If an interior vertex lay in an infinite cluster, that
cluster would be `C'`, `C''` or a third one, and each case gives a pair of
distinct infinite clusters at distance less than `m`. So every interior vertex
lies in a finite cluster.

By countability, a fixed path `gamma` realises this configuration with
positive probability. Open the edges `v_0 v_1, ..., v_{m-2} v_{m-1}` and close
`e = v_{m-1} v_m`. That last edge was already closed, since `v_{m-1}` is not in
`C''`. Opening edges only merges the clusters of `v_0, ..., v_{m-1}`, and none
of those clusters is `C''`. So in the modified configuration minus `e`, `v_{m-1}`
lies in an infinite cluster containing `C'`, and `v_m` lies in `C''`, which is
distinct.

The modification changes finitely many edges and `0 < p < 1`, so the modified
event has positive probability. By `Gamma`-invariance, some edge at the root has
the same property, so `Delta(p) > 0`.

*Integral.* `fpbs-msf-excess-equals-nonuniqueness` gives
`delta_G = (1/2) sum_{e ∋ o} integral_0^1 P(endpoints in different infinite clusters of omega_p \ e) dp`,
which is `(1/2) integral_0^1 Delta(p) dp`.

## Part (C): finite minimal spanning forests

With iid uniform labels, `e = xy` lies in the minimal spanning forest of a
finite graph if and only if no path in `omega_{U(e)} \ e` joins `x` to `y`.
Hence `P_n(e in MSF_n) = integral_0^1 P_n(x not connected to y in omega_p \ e) dp`.

By independence, `P_n(x <-> y in omega \ e) = P_n(e closed, x <-> y)/(1-p)`.
The Part (D) sandwich, with the `L_R` contribution kept, gives for
`p != p_c(G)`:

`E_n sum_{y ~ o_n} 1{e closed, o_n <-> y} -> sum_{y ~ o} P_G(e closed, o <-> y or both infinite)`.

Therefore
`E_n sum_{y ~ o_n} P_n(o_n not connected to y in omega \ e)` tends to
`sum_{y ~ o} P_G(o not connected to y in omega \ e, not both in infinite clusters of omega \ e)`.

The integrands are bounded by `D`, so dominated convergence in `p` applies. By
the definition of the wired minimal spanning forest (Lyons--Peres--Schramm,
arXiv:math/0412263), `e` is excluded from `WMSF` exactly when it is the
largest-label edge of a cycle or of a bi-infinite path. For an edge `e`, this
happens exactly when its endpoints are joined in `omega_{U(e)} \ e` or both lie
in infinite clusters of `omega_{U(e)} \ e`. So the limit is
`E deg_WMSF(o)`, which is `2` by LPS Proposition 3.6 as recorded in
`fpbs-msf-excess-equals-nonuniqueness-proof`.

As an independent check, `E_n deg_{MSF_n}(o_n) = 2(1 - k_n/n) <= 2`, where
`k_n` is the number of components.

## Calibration

`rrg_glued_calibration.py` runs the configuration-model 3-regular graph with
`n = 200000` and `R = 4`, and compares against the `T_3` values. Here
`eta = 1 - (1 - p eta)^2`, the two-point sum is `3p`, the glued sum is
`3[p + (1-p) eta^2]`, and the defect is `3(1-p) eta^2`. Every row of
`output-n200000-R4-seed1.txt` agrees to within `0.005`, and `|C_2|/n <= 0.0012`
at every tested `p`. So the finite data match the glued law, and they differ
from the ordinary two-point function by exactly the defect.
