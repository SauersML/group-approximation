---
rg: 2
id: toms-schubert-algebra-continuous-ranks-are-constant
kind: claim
title: In Toms's no-Gamma AH algebra every positive element with finite continuous rank function has constant rank
distinct_from:
  doubling-ah-finite-stage-continuous-ranks-are-constant: that proves constancy only for finite-stage elements and countable orthogonal sums of them; this asserts it for every positive element of B tensor K, including genuine Cuntz suprema.
  toms-schubert-algebra-misses-a-rank: that asks for one unrealized continuous affine function; this asserts the much stronger rigidity that no non-constant continuous function is a rank, and implies that claim.
---

**OPEN.** Let `B` be Toms's simple AH algebra without uniform property Gamma
(arXiv:2606.12188v2, Proposition 4 and Theorem 5). If `a in (B tensor K)_+` and
`tau -> d_tau(a)` is finite and continuous on `T(B)`, then `d(a)` is constant.

The same assertion for the non-simple limit `A` of Toms's Section 4 (no
point-evaluation summands, `delta = 1`) is the test case.

**Consequence.** `T(B)` is the Poulsen simplex, so non-constant strictly
positive continuous affine functions exist. A realizer of such an `f` would have
continuous rank `f`. So this claim gives `toms-schubert-algebra-misses-a-rank`
and refutes STW XXIII for `B` (route
`toms-schubert-algebra-misses-a-rank-via-constant-ranks`).

**Model test.**
- *A trivial model fails it.* In a simple first-type Villadsen algebra with more
  than one trace (stable rank one, so all ranks occur by Thiel), non-constant
  continuous ranks exist. There
  the unit at the first stage is a trivial bundle and the connecting maps carry
  no line-bundle twists.
- *Load-bearing hypothesis.* If some `X_M` were disconnected, a projection on
  one component would have a continuous non-constant rank.
- *Real object.* Unknown. That is the claim.

## Attempts

- **Reduction to coherent near projections.** Let `d(a)` be continuous and put
  `h_eps(t) = min(1, max(0, (t - eps)/eps))`. Dini's theorem makes
  `tau -> tau tensor Tr(h_eps(a))` converge uniformly to `d(a)`, since these
  functions are continuous (Rørdam's lemma, as in Corollary B of
  `toms-schubert-algebra-fails-o6-plus`). So:
  - the defects `sup_tau tau tensor Tr(h_eps(a) - h_eps(a)^2)` tend to `0`;
  - the uniform unnormalized 2-norm distances between `h_eps(a)` and
    `h_eps'(a)` tend to `0`.
  Approximating at finite stages gives near projections `z_j` in `M_(n_j)(B_(L_j))`
  whose traces converge uniformly to `f`, whose defects tend to `0`, and which are
  **Cauchy** in uniform 2-norm. Rank density alone supplies the first two
  properties (`rank-density-is-quadratic-trace-selection`). Only the Cauchy
  property is new, so an obstruction must attack coherence across stages.
- **Single-stage near projections of non-constant profile exist.** Use Toms's
  trivial `p_1 = theta^d` and a scalar `h in C(X_1)` with values in `[a, b]`.
  - At stage `L` the bundle `p_L` is a sum over `N = 2^(L-1)` leaves of
    `theta^d tensor gamma_l`. Choose nested constant subspaces `W_m` and put
    `E_m = sum_(l <= m) W tensor gamma_l`.
  - Ramping through the chain `E_0 ⊂ ... ⊂ E_N` as a function of the leaf average
    `(1/N) sum_l h(x_l)` gives a near projection at **every** point of `X_L`.
    Its profile is about `tau(h)` and its defect is at most one increment,
    about `1/N`.
  So pointwise near projections of non-constant profile are cheap. A leafwise
  product construction fails instead: all leaf coordinates can sit at their
  thresholds at once.
- **Where coherence costs (heuristic, unproved).** Push the stage-`L` element to
  stage `L + k`.
  - Each of the `2^k` twisted sub-blocks ramps as a function of its own leaf
    average. At points where every sub-block sits at a threshold, the defect is
    still about `1/N`.
  - Splitting increments within a sub-block is free, but only down to rank-one
    pieces.
  - Going below that granularity needs rotation between sibling sub-blocks.
    Moving a rank-one piece from `gamma_1` to `gamma_2` at a tree node is a
    section of `O(-1)` tensor pullbacks over that node's factor `CP^(j)`, with
    nonzero top class, so it vanishes somewhere.
  - Distinct nodes use distinct `CP` factors, so the Künneth product of their
    classes is nonzero. By the propagation argument of Toms's Lemma 1, the direct
    sum of all merges should degenerate at one common point.
  - This suggests **fuzz persistence**: the worst-point defect of a Cauchy
    sequence stays bounded below by the granularity of its first stage, which
    contradicts defect tending to `0`.
  - *Where it dies.* A general Cauchy sequence need not transport mass through
    node swaps. No invariant yet turns 2-norm closeness of two near projections
    at every point into a bundle map with bounded kernel between their fuzzy
    parts, the analogue of Toms's Theorem 2. In `B` the fresh point-evaluation
    summands are trivial blocks, but maps from twisted pieces into them are still
    sections of nontrivial line bundles over `CP` factors.
