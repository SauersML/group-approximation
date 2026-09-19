---
rg: 2
id: folded-dkkms-line-hosts-have-uniform-spectral-gap
kind: claim
title: At l = 1 the folded DKKMS 2-to-1 host has spectral gap at least 1 - sqrt(rho_k + 2 delta) > 0.1, with rho_k = (3/4)/(1 - 4^(-k)) and delta = C(k,2) c_D / |Eq|, for every beta in [0,1], every k >= 2 and every regular 3LIN source whose equations pairwise share at most one variable, because the Lemma 4.1 classes are exactly the fibres of the singled-out set S and the S-to-tuple walk contracts every Efron-Stein level by (3/4)^|T|
distinct_from:
  folded-dkkms-hosts-keep-spectral-gap-as-smoothing-vanishes: that conjectures a lower bound c(l) > 0 for every l; this proves it for l = 1 only, where the B-side Grassmann fibre is trivial, and leaves l >= 2 open there.
  folded-dkkms-host-gap-vanishes-as-l-grows: that is a proved upper bound 2(beta + 6 * 2^(-l)) for l >= 6; this is a proved lower bound at l = 1, and the two do not overlap in l.
artifacts:
  - experiments/ugc-folded-gap-2026-09-17/folded_l1_gap.py
---

**ESTABLISHED.** Route: `folded-dkkms-line-hosts-gap-proof`.

## Setting

This is the folded DKKMS 2-to-1 game of ECCC TR16-198, Section 4.2, with
`l = 1`, quoted in the route. The ingredients are:
- A 3LIN source `(X, Eq)` on `n` variables, with `N = |Eq| = nD/3`. It
  satisfies two conditions:
  - (R1) every variable lies in exactly `D` equations;
  - (R2) two distinct equations share at most one variable.
- `𝒰`, the set of legitimate `k`-tuples, meeting conditions (a) and (b) of the
  paper.
- `A = {(U, L) : L ∈ Gr(X_U, 1), L ∩ H_U = 0}`, `B = {(V, L')}`, smoothing
  `β ∈ [0, 1]` and the edge law of (D3) conditioned on `L ∩ H_U = 0`.
- Folding by `C(U0, L0) = {(U, L) : L + H_U + H_U0 = L0 + H_U + H_U0}`, with
  the weights summed.

`λ_2 = 1 − σ_2` of the normalized bipartite matrix of the folded graph. This is
the normalized-Laplacian `λ_2` of the gate in
`orientation-lift-selectors-need-vanishing-host-gap`.

## Theorem L

Put
- `ρ_k = (3/4) / (1 − 4^(−k))`, so `ρ_2 = 4/5` and `ρ_k ↓ 3/4`;
- `c_D = 1 + 3(D − 1) + 6(D − 1)²`;
- `δ = C(k, 2) c_D / N`.

If `k >= 2` and `δ <= 1/2`, then for every `β ∈ [0, 1]`:

```text
σ_2(folded)² <= ρ_k + δ/(1 − δ),     λ_2(folded) >= 1 − sqrt(ρ_k + 2δ).
```

For `δ <= 0.002` this is `> 0.1`, uniformly in `k`, `β` and the gap of the
source. At fixed `k` and `D`, as `n −> ∞`, the bound tends to
`1 − sqrt(ρ_k)`. That is `0.1056` at `k = 2` and tends to `1 − sqrt(3/4) ≈ 0.134`
as `k` grows, which is the "mechanism prediction" `0.134` recorded in the
target conjecture.

### Lemma A (the l = 1 classes, exactly)

For `v ∈ X_U \ H_U`:
- let `r(U, v)` be the unique vector of `v + H_U` with weight at most 1 on each
  block;
- let `S(U, v) = supp r`, a nonempty *partial transversal* of `U`, meaning one
  variable in each non-free block.

Under (b) and (R2), `(U', span v') ∈ C(U, span v)` holds iff
`S(U', v') = S(U, v)`. So the relation is an equivalence and needs no closure.
The class of `S` is `{(U', span v') : U' ∈ Cov(S), v' ∈ 1_S + H_U'}`, where
`Cov(S) = {U' ∈ 𝒰 : S ⊆ vars(U')}`. It has exactly `2^k |Cov(S)|` members.

This settles prerequisite (P1) of the target at `l = 1`, exactly and not only up
to `o(1)` mass. The target's shortfall in exact mass (0.93–0.97) came from
dropping legitimacy (b). Without (b), the relation is not an equivalence; see
the numerics below.

## Why the proof is uniform

- **Smoothing.** `S – U – V` is a Markov chain, so smoothing can only lower
  `σ_2`. This gives (P5) at `l = 1`.
- **Two-step walk.** `σ_2²` is the second eigenvalue of the two-step walk
  `U −> S −> U'`, where `S` is uniform over the `4^k − 1` nonempty partial
  transversals and `U'` is uniform over `Cov(S)`.
- **Ordered lift.** Lifting to ordered tuples in `Eq^k` writes that walk as a
  mixture over the free set `F`. Here `F` is a Bernoulli(1/4)^k set conditioned
  on `F ≠ [k]`. For each `F`:
  - the coordinates in `F` are resampled from the uniform measure on `Eq`, up
    to the legitimacy defect `δ` (this is (P3));
  - the others pass through a norm-1 kernel.
- **Efron–Stein.** The level-`T` part survives only when `T ∩ F = ∅`, which has
  probability `(3/4)^|T| / (1 − 4^(−k)) <= ρ_k`.
- **No source gap.** The source's expansion enters only through the norm-1
  kernel, whose norm is bounded by 1 regardless. So the gap of the source is
  never used.

## Scope and impact

- **Degenerate alphabet.** At `l = 1` the B-side space `Gr(X_V, 0)` is a
  single point. Each folded A-vertex carries one line, and the 2-to-1 game is
  degenerate as a hardness instance: DKKMS soundness needs `l` large. So
  Theorem L does not by itself kill or confirm any selector on the DKKMS
  instances that are actually used.
- **What it does settle.**
  - It proves the target's mechanism at `l = 1`: (P1) exactly, (P3) with an
    explicit `δ`, and (P5).
  - It shows that the folded gap is independent of `β`, `k` and the source gap
    at `l = 1`.
  - It refutes, at `l = 1`, any forecast that the folded gap is `O(β)` or
    decays with `k`.
- **Where l >= 2 fails.** For `l >= 2` the same route breaks at a named step.
  The free set `F` must lie inside the blocks that `L'` misses, so its law
  depends on the B-state, and the ordered lift no longer factors. In addition,
  `(V, L')` depends on `L`, so the Markov chain `C – U – B` fails. Theorem F
  (`folded-dkkms-host-gap-vanishes-as-l-grows`) shows that at large `l` the
  gap does go to 0, so no `l`-uniform version exists.

## Numerics

`folded_l1_gap.py`, with seed 20260918, uses random sources satisfying (R1) and
(R2) with `D = 2`.

**(1) Lemma A.** Union-find closure of the defining relation over all
overlapping tuple pairs, compared with the fibres of `S`:

| n | k | (b) imposed | tuples | union-find classes | S-fibres | pairs with v ∈ H_U+H_U' | agree |
|---|---|---|---|---|---|---|---|
| 24 | 2 | yes | 58 | 227 | 227 | 0 | True |
| 24 | 2 | no | 96 | 210 | 294 | 0 | False |
| 30 | 2 | yes | 113 | 383 | 383 | 0 | True |
| 30 | 2 | no | 160 | 355 | 456 | 0 | False |
| 24 | 3 | yes | 27 | 624 | 624 | 0 | True |
| 24 | 3 | no | 271 | 626 | 2137 | 351 | False |

**(2) Gap.** At `β = 0`, which is the worst case by the Markov-chain step:

| n | k | λ_2 | limit bound `1 − sqrt(ρ_k)` |
|---|---|---|---|
| 30 | 2 | 0.1964 | 0.1056 |
| 60 | 2 | 0.1605 | 0.1056 |
| 120 | 2 | 0.1367 | 0.1056 |
| 240 | 2 | 0.1288 | 0.1056 |
| 30 | 3 | 0.2314 | 0.1271 |
| 60 | 3 | 0.2021 | 0.1271 |
| 90 | 3 | 0.1767 | 0.1271 |

All values are above the limit bound. The finite-`n` bound
`1 − sqrt(ρ_k + 2δ)` is weaker, and is vacuous at these small `n`. With
`D = 2`, the gap decreases in `n` toward the limit bound. This is consistent
with the bound being approached when the equation–variable walk of the source
has eigenvalue near 1. That is the case for sparse `D = 2` sources, where the
norm-1 kernel of the route is nearly tight. Tightness is not proved.
