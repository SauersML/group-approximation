---
rg: 2
id: single-density-expansion-forces-the-multiscale-profile
kind: claim
title: A regular graph with Phi_H(1/q) >= 1 - eta satisfies the multiscale profile Phi_H(A) >= 1 - nu/24 for every mu(A) in [1/q, tau], with loss independent of tau q, so N2 is forced on the NO outputs of a lift reduction and not only at scale 1/q
distinct_from:
  lifts-over-multiscale-expanders-expand-unless-ug-value-large: that assumes the multiscale profile (N2) as a hypothesis of its sufficiency half, and its necessity half forces expansion only at the single density 1/q (its own item (4) says "N1 at level nu and N2 at scale 1/q"); this is the missing propagation from that single density to the whole window [1/q, tau], which that claim neither states nor proves.
  sseh-lift-routes-need-spectrally-defective-bases: that is the reduction-level spectral gate whose step (B3) needs this propagation; this is the propagation itself, a statement about one graph with no reduction, no unique game and no complexity hypothesis.
  lift-yes-sets-are-labelings-unless-the-base-loses-a-cut: that decodes one non-expanding set of a lift into a labeling plus a cut of the base; this says nothing about lifts or labels and only compares the base's expansion profile at two densities.
  small-set-expansion-hypothesis: that is the hardness conjecture; this is an unconditional graph-theoretic implication between expansion at one density and expansion across a window, with no complexity content.
  commuting-hamiltonians-on-small-set-expanders-in-np: that is an algorithmic consequence of small-set expansion for local Hamiltonians; this is a purely combinatorial scale-propagation question about the expansion profile itself.
---

**OPEN.** Recorded 2026-09-18 (swarm-0917) as the hole that refereeing opened in
step (B3) of `sseh-lift-base-spectral-gate-proof`.

*Setting.* `H` is a regular multigraph on `V` with uniform `mu`, `q >= 2`,
`delta = 1/q`, `tau >= 2/q`, `|V| >= q`, and `nu in (0, 1/2]`. As usual
`e(A) = Pr[u in A, v in A] = mu(A)(1 - Phi_H(A))`, and
`Phi_H(rho) = min_(mu(A) = rho) Phi_H(A)`.

**Statement.** There is a function `eta = eta(nu)` (independent of `q` and
`tau`) such that

```text
Phi_H(1/q) >= 1 - eta    ==>    Phi_H(A) >= 1 - nu/24  for every A with
                                mu(A) in [1/q, tau].
```

Equivalently: the multiscale profile (N2) of
`lifts-over-multiscale-expanders-expand-unless-ug-value-large` is a consequence
of near-perfect expansion at the single density `1/q`, with no loss that grows
with `tau q`.

**Why it is wanted.** The necessity half (item (3)) of
`lifts-over-multiscale-expanders-expand-unless-ug-value-large` forces exactly
two things on the NO outputs of a reduction that proves SSEH through
label-extended graphs: `val(U) <= nu` and `Phi_H(W) >= 1 - nu` for `mu(W) = 1/q`
— that is, N1 at level `nu` and N2 **at scale `1/q` only**. Step (B3) of
`sseh-lift-base-spectral-gate-proof` needs the profile on the whole window
`[1/q, tau]`: it excludes the Cheeger cut `B` from `[1/q, tau]` using
`Phi_H(A) >= 1 - nu/24` there, and then runs the padding chain
`mu(B)(1 - kappa) <= e(B) <= e(B') <= (2/q)(nu/24)` at a set `B'` of measure in
`[1/q, 2/q]`. With this claim, (B3) and hence (P4) of
`sseh-lift-routes-need-spectrally-defective-bases` become unconditional; without
it they are conditional on N2 being supplied by hand.

## Attempts

* **Random halving (the obvious propagation), 2026-09-18.** For `A` with
  `mu(A) = k/q`, split `A` into `k` random pieces of measure `1/q` each. Each
  piece `A_i` has `E[e(A_i)] ~ e(A)/k^2`, and `e(A_i) <= (1/q) eta` by
  hypothesis, so `e(A) <= k eta / q`, i.e. `1 - Phi_H(A) <= k eta`. Where it
  dies: the loss is linear in `k = q mu(A)`. The bound is vacuous once
  `k >= 1/eta`, i.e. once `mu(A) >= 1/(eta q)`. For fixed `eta` and
  `q -> infinity` — the SSEH regime, in which `delta = 1/q` must go to zero
  while `eta` stays fixed — the entire upper part of `[1/q, tau]` for constant
  `tau` is left unconstrained. Any proof must beat the `k^2` versus `k`
  mismatch in the second-moment step, i.e. get a loss independent of `tau q`.
* **Weakly coupled clusters: an apparent counterexample, 2026-09-18
  (refereeing, lens 2; sketch only, not yet replayed).** Fix `rho` with
  `1/q << rho <= tau` and take `H` to be `1/rho` noisy-cube-like clusters of
  measure `rho` each, joined by a vanishing coupling. Inside a cluster a set of
  measure `1/q` has relative density `(1/q)/rho -> 0`, so it expands: the
  construction has `Phi_H(1/q) >= 1 - eta`. But a whole cluster is a set of
  measure `rho` strictly inside `[1/q, tau]` with expansion `O(coupling)`, and
  `lambda_2(H) -> 0`. That is exactly a violation of the statement above, and
  also exactly the configuration that (B3) asserts cannot occur. Where it stops:
  the cluster expansion at density `1/q` across the coupling has not been
  computed here, and no replay was run, so this is recorded as the leading
  attack on the claim rather than as a refutation. If it is made exact, this
  claim should be flipped to a refuted one and (B3), (P4) and the title of
  `sseh-lift-routes-need-spectrally-defective-bases` must keep N2 as an explicit
  hypothesis permanently rather than await a proof.
* **Deferred: the weaker form that would still serve (B3).** (B3) does not need
  the full window: it needs (a) enough of `[1/q, tau]` excluded to place the
  Cheeger cut, and (b) the single scale `[1/q, 2/q]` for the padding step. Half
  (b) is already forced by the necessity half up to the constant
  (`e(B') <= (2/q) eta` rather than `(2/q)(nu/24)`). So a strictly weaker claim —
  the profile on `[1/q, tau]` with the constant degraded from `nu/24` to any
  bound below `1/2 - kappa` — would suffice, and is not obviously killed by the
  halving loss for `tau = O(1/(eta q))`. That restricted range has not been
  worked out.
