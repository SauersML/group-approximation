---
rg: 2
id: degree-blow-up-extends-spectral-gap-gate-to-irregular-hosts
kind: claim
title: The degree blow-up turns every loop-free weighted unique game into a loop-free regular one with the same optimum and lambda_2 = min(lambda_2, 1), so the AKKSTV spectral-gap gate kills irregular and biregular bipartite YES hosts too
distinct_from:
  spectral-gap-ratio-reductions-cannot-prove-ugc: that proves the gate (K1) only for loop-free regular YES outputs and lists irregular or looped outputs as survivor (S1); this closes the loop-free half of (S1) by a value- and spectrum-preserving reduction to the regular case, with lambda_2 capped at 1.
  unique-games-on-expanding-constraint-graphs-are-easy: that is the imported AKKSTV rounding, whose quoted proof uses the regular characterization (7); this does not re-read the import, it maps every loop-free weighted instance to a regular one before applying it.
artifacts:
  - experiments/ug-blowup-regularization-2026-09-18/check_blowup.py
---

**ESTABLISHED.** Route: `degree-blow-up-gate-proof`. It uses only the
established `spectral-gap-ratio-reductions-cannot-prove-ugc` (gate (K1)) and
elementary linear algebra.

This answers live need `6166cb1b` ("does the AKKSTV rounding survive on
biregular bipartite constraint graphs?") with **YES**, in the stronger form "on
every loop-free weighted constraint graph", by the second of the two ways the
need allowed: a value-preserving regularization.

## Setting

Notation is that of `spectral-gap-ratio-reductions-cannot-prove-ugc`. A unique
game `U` is a finite multiset of constraints `x_v = π_e(x_u)` over a finite
alphabet, with positive integer multiplicities `w_e`, no isolated vertex and
(here) **no loops**. `deg(u)` is the weighted degree, `W` the total weight, and
`λ_2(U)` the second smallest eigenvalue of the normalized Laplacian
`I − D^(−1/2) A D^(−1/2)`. `X(s)` is the constant of (K1): the least integer
`x >= 3` with `C_A log(x)/x < 1 − s`.

**Degree blow-up `B(U)`.** Replace each vertex `u` by `m_u := deg(u)` copies
`u_1, ..., u_(m_u)`. Replace each constraint `e = (u, v, π_e)` by the `m_u m_v`
constraints `(u_i, v_j, π_e)`, each of weight `w_e / (m_u m_v)`. Rescale all
weights by one common integer to make them multiplicities, as (K2) of the parent
does; rescaling changes neither values nor `λ_2`.

## Statements

**Theorem 1 (blow-up).** For every loop-free `U`:

1. `B(U)` is loop-free, and every copy has weighted degree exactly `1` before
   rescaling. So `B(U)` is regular.
2. `opt(B(U)) = opt(U)`.
3. The normalized-Laplacian spectrum of `B(U)` is the spectrum of `U` together
   with the eigenvalue `1`, of multiplicity `sum_u (m_u − 1)`. Hence
   `λ_2(B(U)) >= min(λ_2(U), 1)`, with equality when some `m_u >= 2`.
4. `B(U)` has `2W` vertices and at most `sum_e m_u m_v <= W^3` distinct
   constraints. It is computed in time polynomial in `W` and the alphabet size.

**Theorem 2 (the gate on irregular hosts).** Fix `s < 1`. Let `f` be a
polynomial-time reduction from a language `L` whose outputs are loop-free unique
games of total multiplicity `W(f(x)) <= poly(|x|)`, such that:

* `x in L` implies `λ_2(f(x)) > 0` and `min(λ_2(f(x)), 1) >= X(s)(1 − opt(f(x)))`;
* `x notin L` implies `opt(f(x)) <= s`.

Then `L in P`. No regularity is assumed.

**Corollary 3 (bipartite hosts).** A connected loop-free bipartite graph with at
least three vertices has `λ_2 <= 1`: its normalized-Laplacian spectrum is
symmetric under `λ -> 2 − λ`, so `2 − λ_2` is an eigenvalue other than `0`,
hence `2 − λ_2 >= λ_2`. For such hosts, including the biregular bipartite ones
of need `6166cb1b`, the hypothesis of Theorem 2 is exactly the parent's
`λ_2 >= X(s)(1 − opt)`.

## Where every member dies

At the YES output, before any soundness analysis, exactly as in (K1). The
invariant is `min(λ_2, 1) / (1 − opt)` on YES outputs, now for every loop-free
weighted constraint graph. A reduction to `Gap-UG[1 − η, s]` whose loop-free
YES outputs keep `λ_2` above `X(s) η` puts its source in P.

## Survivors (not killed)

* **(S1') Loops.** Blowing up a loop at `u` creates constraints between copies
  of the same vertex, and the random-copy argument of item 2 then needs two
  independent copies of one vertex. Looped outputs stay outside.
* **(S1'') Superpolynomial multiplicities.** The blow-up has `2W` vertices. For
  weights given in binary with exponential total, one would first round
  weights; that step is not proved here.
* Survivors (S2) and (S3) of the parent are untouched.

## Artifact

`check_blowup.py` builds 40 random loop-free weighted unique games (general,
bipartite, and orientation lifts of random 2-to-1 games with alphabet `[4]`
over `[2]`). It checks items 1 and 3 exactly (regularity in `Fraction`s,
spectrum by `numpy` to `1e-8`, including cases with `λ_2(U) = 2 > 1` where
`λ_2(B) = 1`), and item 2 by brute force on the 17 instances with at most 7
blown-up vertices, including the random-copy averaging identity. All pass.
