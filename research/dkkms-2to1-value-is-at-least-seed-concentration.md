---
rg: 2
id: dkkms-2to1-value-is-at-least-seed-concentration
kind: claim
title: On every triple-simple 3LIN instance the folded DKKMS 2-to-1 game and its quotient free-bit lift have value at least one minus the class seed spread xi, by an instance-free blockwise labelling, so DKKMS soundness forces a flat seed law and a smoothing rate O(sqrt(l/k)), and soundness at any fixed smoothing rate is false
distinct_from:
  dkkms-quotient-free-bit-lifts-seed-mass-to-unique-games: that proves YES lift value >= 1 - xi - eps_out from an honest global assignment; this proves value >= 1 - xi - mu_sp on EVERY triple-simple input, NO inputs included, from a local labelling that reads no assignment, so the same seed concentration that gives that node its completeness removes all soundness.
  dkkms-2to1-game-sound-at-heavy-smoothing: that is the hole this refutes.
  dkkms-seed-law-is-uniform-in-regime-and-far-in-window: that proves the seed law is flat at beta = log log k / k; this shows flatness is necessary for any soundness, at every parameter point, not only a feature of the published rate.
  dkkms-near-perfect-labellings-are-outer-honest: that says near-1 labellings are close to locally honest patchworks of per-tuple outer labellings; the labelling here is such a patchwork, built from block-local assignments, and it has value near 1 exactly when the seed is identifiable.
  unique-constraints-orient-at-most-half-of-a-fiber: that caps completeness of orientations of perfect games; this is a soundness collapse of one explicit composed family, with no orientation hypothesis.
artifacts:
  - experiments/dkkms-heavy-smoothing-local-labelling-2026-09-19/check_local_labelling.py
---

**ESTABLISHED.** Route: `dkkms-2to1-value-is-at-least-seed-concentration-proof`.

## Setting

The instance is the folded DKKMS game `G(I; l,k,beta)` of ECCC TR16-198 §4.2,
as quoted verbatim in `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`,
at any `l >= 2`, `k >= 1` and any smoothing rate `beta in [0,1]`. The notation
follows `dkkms-quotient-free-bit-lifts-seed-mass-to-unique-games`:

- `Y = X_U / H_U = ⊕ Y_i`, with `Y_i = F_2^3/<111>`, and `pi_i : Y -> Y_i` the
  block projection;
- the class `C` of `(U,L)` has `S_C = L + H_U` and `Lbar = S_C / H_U`;
- the seed of an edge is `Q = (L' + H_U)/H_U`, a hyperplane of `Lbar`;
- `w(Q | C)` is the class seed law and `xi(l,k,beta) = E_C [1 - max_Q w(Q|C)]`,
  with `C` drawn by edge mass.

Here a class is read, as in that node, as the pair `(U, S_C)` of a tuple and
its space. Given `U`, the edge process does not read the instance, so `w` and
`xi` do not depend on `I`.

An instance is **triple-simple** if no two of its equations have the same
variable triple. Regular triple-simple instances of value at most `s` exist for
every `s > 1/2` (route, Step 9). On such an instance, a folding class of the
paper can contain two different tuples only if `Lbar` contains a nonzero vector
supported on at most 3 blocks. That edge mass is at most
`mu_sp(l,k) := 11 * 2^l k^3 2^(-k)`.

## Statements

**Theorem LV (instance-free value).** For every triple-simple 3LIN instance
`I` (satisfiable or not), and all `l >= 2` and `k >= l + 1` and `beta`,

```text
val(G_folded(I; l,k,beta)) >= 1 - xi(l,k,beta) - mu_sp(l,k),
val(G_multi(I; l,k,beta))  >= 1 - xi(l,k,beta) - mu_sp(l,k),
val(Lift(G(I; l,k,beta)))  >= 1 - xi(l,k,beta) - mu_sp(l,k),
```

where `Lift` is the quotient free-bit lift of
`dkkms-quotient-free-bit-lifts-seed-mass-to-unique-games`. The labelling is
explicit and reads only the equations of each tuple.

- **A at class `C`.** Pick `Q*(C)`, a most likely seed. For each block `i`
  with equation `e_i` (right-hand side `b_i`):
  - if `pi_i(Q*) = <ebar_v>` is one-dimensional, `x_i` is the satisfying
    assignment of `e_i` with `x(v) = 0` (the least other variable carries `b_i`);
  - otherwise `x_i` is the canonical satisfying assignment `c_(e_i)`.

  The class label is `x` restricted to `R_C`. For the lift, it is corrected to
  `x + x(y_C) phi_C`, so that it reads `0` on the free-bit vector.
- **B at `(V, L')`.** On a kept block the rule is the same, applied to the true
  block image `pi_i(Q)` (B knows `e_i`). On a smoothed block with variable `v`,
  `y(v) = 0`. The label is `y|_(L')`, and the free bit is `0`.

Whenever `Q*(C)` is the seed of the edge, the constraint holds exactly. In a
smoothed block, `L'` sees only `e_v`, and both sides put `0` there. In a kept
block, both sides use the same rule on the same data. So the value is at least
`Pr[Q* = Q] - mu_sp = 1 - xi - mu_sp`. The same holds with `Q*` replaced by
the polynomial-time rule `P*` of Lemma ID, with `Pr[P* = Q]` in place of
`1 - xi`.

Instances with repeated triples are not covered. There, twin tuples that
differ only in right-hand sides share a folding class, and the argument does
not handle them.

**Lemma ID (the seed is identifiable under heavy smoothing).** Let `l >= 3` and
`Delta_l = 1/2 - 2^(1-l) >= 1/4`. The polynomial-time rule "take the
hyperplane `P` of `Lbar` that maximises `#{i : dim pi_i(P) <= 1}`" finds the
seed, for `k >= l + 1`, except with probability at most
`eps_ID(l,k,beta) + 2^(l-k)`, where

```text
eps_ID(l,k,beta) = [ (2^l - 2) exp(-beta^2 Delta_l^2 k / 8) + exp(-beta k / 8) ] / (1 - 2^(l-k)).
```

Hence `xi(l,k,beta) <= eps_ID(l,k,beta) + 2^(l-k)`. At fixed `(l, beta)`
this tends to `0` as `k` grows.

**Corollary R (refutation).** `dkkms-2to1-game-sound-at-heavy-smoothing` is
false. Fix `delta < 1`, and any `l >= 3`, `beta in (0,1)`, `s in (1/2,1)` and
`k_1`. Take `k >= k_1` with `eps_ID + 2^(l-k) + mu_sp < 1 - delta`. Every
regular triple-simple instance of value `<= s` (and they exist) then maps to a
game of value `> delta`. So the route
`ugc-from-dkkms-soundness-at-heavy-smoothing` is dead.

**Corollary SC (smoothing ceiling).** Let `l >= 3`, and let `k` be large
enough that `2^(l-k) <= 1/3` and `2^(l-k) + mu_sp(l,k) <= (1-delta)/4`.
Suppose the DKKMS 2-to-1 reduction at `(l,k,beta)` has soundness `delta < 1`
on even one triple-simple instance. Then the seed law is flat on average,
`E_C max_Q w(Q|C) <= delta + mu_sp`, and

```text
beta <= max( sqrt( 8 ln(2^(l+3)/(1-delta)) / (Delta_l^2 k) ),  8 ln(8/(1-delta)) / k ).
```

So `beta = O(sqrt((l + ln(1/(1-delta)))/k))`. The published requirement
`beta sqrt(k) 2^l << 1` of the smooth-advice step (DKKMS Lemmas 4.10 and 5.3)
lies inside this necessary region, and the rate `beta = log log k / k` lies far
inside it. Every soundness proof for this construction has to work below the
ceiling. Beating the published proof is possible only in the window
`2^(-l)/sqrt(k) <~ beta <~ sqrt(l/k)`.

**Corollary FB (the free bit carries no gap).** At every parameter point with
`k >= l + 1`, on triple-simple instances,
`val_YES(Lift) - val_NO(Lift) <= xi + mu_sp`. So the free-bit lift cannot give
hardness anywhere on them:

- where it is near-complete (`xi` small), it has no soundness;
- where DKKMS is sound (`xi >= 1 - delta - mu_sp`), its completeness guarantee is only
  `1 - xi - eps_out <= delta + mu_sp`.

The argument extends to any orientation lift whose pinned direction is a
function of the class and its seed, with a pinned bit that the B-label carries.

## Class kill (impact type 3)

- **Invariant.** The class seed spread `xi`, equivalently the mean maximal seed
  posterior `E_C max_Q w(Q|C)`.
- **Where every member dies.** It dies at soundness, because Theorem LV gives
  `val >= 1 - xi - mu_sp` on every triple-simple input, NO inputs included.
- **What is killed.** Every route to UGC or Rich 2-to-1 through a DKKMS-type
  Grassmann composition of the smooth 3LIN outer game at a rate where the
  A-side can locate the smoothed blocks. That covers the free-bit route, every
  fixed-rate variant, and every rate above the ceiling of Corollary SC.
- **Mechanism.** The outer game is sound only because A does not know which
  blocks of its tuple were smoothed. The Grassmann seed exposes, block by
  block, exactly the coordinate that the constraint tests (`e_v` in a smoothed
  block). A labelling that fixes those exposed coordinates to `0` and completes
  each equation locally is consistent across all tuples, with no global
  assignment. So smoothing that is heavy enough to make the seed identifiable
  also hands the provers a local strategy.

## Checks

`experiments/dkkms-heavy-smoothing-local-labelling-2026-09-19/check_local_labelling.py`
prints ALL PASS. It checks:

- on 3,040 sampled edges (`k` up to 3000, `l` = 3 to 5, `beta` in
  {0.25, 0.5, loglogk/k}, with random right-hand sides), that A's assignment
  satisfies every equation of its tuple;
- that the constraint holds on a basis of `L'` every time the seed is
  identified, with 0 failures;
- that the identification rate at `beta = 0.5` and `l = 3` is 0.817 at
  `k = 50`, 0.95 at `k = 100`, and 1.000 at `k = 200`, 400 and 3000;
- that at `beta = log log k / k` the rate is about 0.15 to 0.18, near the flat
  value `1/7`;
- the Hoeffding bound of Lemma ID, which is non-vacuous at `k = 3000`
  (bound 0.017, observed 0).

## Attempts

- **2026-09-19, swarm-0917-w16-w16-ugc-follow.** This node was built as a
  refutation of the last hole of `ugc-from-dkkms-soundness-at-heavy-smoothing`.
  The hole's own heuristic said that copying the dominant B-neighbour would
  work "if folding allowed it", and that the obstacle was a class-consistency
  test of the equations `h_U`. That test is not an obstacle. The class label
  is built from local satisfying assignments of the tuple's own equations, so
  it is folded by construction. The only global coupling, through variables
  shared by different tuples, is cut by setting every exposed variable to `0`.
