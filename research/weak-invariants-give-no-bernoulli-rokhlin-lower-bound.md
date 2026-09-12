---
rg: 2
id: weak-invariants-give-no-bernoulli-rokhlin-lower-bound
kind: claim
title: No weak-equivalence invariant or group invariant bounds Bernoulli Rokhlin entropy below by a positive number
invalidates: [positive-rokhlin-entropy-via-weak-invariant-bounds]
distinct_from:
  every-group-has-positive-rokhlin-entropy-action: that is the open positive-entropy existence hypothesis; this is an obstruction showing that cost, l2-Betti numbers and every other weak-equivalence or group invariant cannot supply the lower bound it needs.
  bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups: that is the open maximality statement on simple Kazhdan hosts; this rules out one class of lower-bound mechanisms for it, on every group.
artifacts:
  - research/artifacts/weak-invariant-blindness-for-bernoulli-rokhlin-entropy-2026-09-12.md
---

**ESTABLISHED.** Let `G` be countably infinite and `Φ` a quantity on free p.m.p. actions of `G`
that is constant on weak-equivalence classes (cost, when `G` is finitely generated) or depends on `G` alone
(ℓ²-Betti numbers, for instance). Then `Φ` has one value `Φ_B(G)` on all nontrivial finite-alphabet
Bernoulli shifts. If `F` is any function with `h^Rok_G(k^G, λ^G) ≥ F(Φ(k^G, λ^G))` for all
nontrivial bases, then `F(Φ_B(G)) ≤ 0`.

Proof: Theorem 3.1 of the artifact. The shifts are weakly equivalent
(`nontrivial-bernoulli-shifts-are-weakly-equivalent`), while `h^Rok ≤ H(λ) → 0` along
`λ = (1−p, p)`. For cost, with `G` finitely generated, this uses
`cost-is-constant-on-weak-equivalence-classes`.

**Consequence.** Cost (on finitely generated groups), ℓ²-Betti numbers, fixed price, and every invariant of approximate finite
statistics of the action cannot prove POS, INF or RBS through a base-independent lower bound, on
any group. Calibration: over `F_2`, every free action has cost `2`, yet the Bernoulli `(1−p, p)`
shift has Rokhlin entropy `H(1−p, p) → 0`. Remark 4.1 of the artifact records what the obstruction
does not touch: lower bounds `h_sup(G) ≥ c(G)` through a group invariant. On Kazhdan hosts, infimal
cost one and Gaboriau's inequality make the first-order candidates vanish (Remark 4.2).
