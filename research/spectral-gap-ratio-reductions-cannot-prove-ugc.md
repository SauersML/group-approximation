---
rg: 2
id: spectral-gap-ratio-reductions-cannot-prove-ugc
kind: claim
title: A reduction to Gap-UG[., s] whose YES outputs are loop-free regular with lambda_2 >= X(s)(1 - opt) puts its source in P, while a padded degree-product shift overlay moves every UG hardness to lambda_2 >= c(1+2c)/(1+c)^3 without raising soundness, so UGC can only live at lambda_2 = O(1 - opt), and Gap-UG[(1-eps)/4, eps] is unconditionally NP-hard on lambda_2 >= 3/8
distinct_from:
  unique-games-on-expanding-constraint-graphs-are-easy: that is the imported rounding algorithm; this turns it into a gate on the YES outputs of reductions, shows the gate is sharp up to a constant under UGC, and adds the unconditional hardness on expanders at completeness 1/4.
  low-label-threshold-rank-reductions-cannot-prove-ugc: that gates the number of label-extended eigenvalues near 1; this gates the second eigenvalue of the constraint graph against the completeness error, a different invariant with a different algorithm behind it.
  entanglement-sound-soundness-cannot-prove-ugc: that kills soundness analyses that also hold against entangled provers; this kills output instance shapes, at the YES case, by a classical spectral algorithm.
  sticky-cylinder-gadget-compositions-cannot-prove-sseh: that kills small-set expansion reductions at the NO case by non-expansion; this kills unique games reductions at the YES case by expansion.
  unique-games-hard-at-completeness-one-half: that is the proved hardness at completeness (1-eps)/2 on arbitrary graphs; this transports it to spectral expanders at completeness (1-eps)/4.
  unique-games-gap-admits-polynomial-time-algorithm: that is the open refutation of UGC on all instances; this refutes nothing, it names a necessary shape of YES outputs.
artifacts:
  - experiments/ugc-calibration-2026-09-17/check_shift_overlay.py
---

**ESTABLISHED.** Proof: `spectral-gap-ratio-kill-proof`. It rests on the
imported `unique-games-on-expanding-constraint-graphs-are-easy` (AKKSTV 2008,
Theorem 2.4) and on `unique-games-hard-at-completeness-one-half`. Everything
else is elementary.

*Setting.* A unique game `U` has `n >= 2` vertices, alphabet a finite group `Γ`
of order `k`, and a finite multiset of constraints `x_v = π_e(x_u)` with `π_e`
a permutation of `Γ` (weights are multiplicities). Loops (`u = v`) are allowed
unless stated otherwise, and no vertex is isolated. `W` is the total weight,
`deg(u)` the weighted degree (a loop counted once) and `vol = sum_u deg(u)`.
`λ_2(U)` is the second smallest eigenvalue of the normalized Laplacian
`I − D^(−1/2) A D^(−1/2)` of the constraint graph. The **invariant** is the
ratio `λ_2(U) / (1 − opt(U))` on YES outputs. `C_A` is the absolute constant of
the imported theorem, and

```text
X(s) = the least integer x >= 3 with C_A log(x)/x < 1 - s.
```

**(K1) Gate.** Fix `s < 1`. Let `f` be a polynomial-time reduction from a
language `L` with these properties:

* `x in L` implies that `f(x)` is loop-free with a regular constraint graph,
  `λ_2(f(x)) > 0` and `λ_2(f(x)) >= X(s) (1 − opt(f(x)))`;
* `x ∉ L` implies `opt(f(x)) <= s`.

Then `L in P`. The decider accepts iff `val(AKKSTV(f(x))) > s`.

*Where every member dies.* At the YES case of the output instance, before any
soundness analysis. Equivalently, unless `L in P`, some loop-free regular YES
output of any reduction to `Gap-UG[1−η, s]` has `opt < 1 − λ_2/X(s)`: the
completeness error must be at least proportional to the spectral gap. In
particular, a route claiming `Gap-UG[1−eps, eps]` hardness from an NP-complete
source on loop-free regular graphs with `λ_2 >= c_0` fixed while `eps → 0`
proves P = NP, and is refuted as a route to the conjecture.

**(K2) Sharpness.** The degree-product shift overlay `O_c` (for rational
`c > 0`) adds, for every pair `u != v` and every `a in Γ`, the constraint
`x_v = x_u a` with weight `c deg(u) deg(v) / (vol k)` (rescaled to integers).
It satisfies:

```text
opt(U)/(1+c) <= opt(O_c U) <= max(opt(U), 1/k),     λ_2(O_c U) >= c(1+2c)/(1+c)^3.
```

Moreover `opt(O_c U) <= opt(U)` and `λ_2 >= 3c/(4(1+c))` when `U` is loop-free,
and `λ_2 >= c/(1+c)` with regularity preserved when `U` is regular.

The padding `U ⊗ m` replaces `Γ` by `Γ × Z_m` and every `π_e` by `π_e × id`. It
keeps `opt` and the constraint graph exactly and makes `1/(km)` as small as
wanted.

Hence **UGC implies** that for every `0 < eps < 1/2`, `Gap-UG[1−eps, eps]` is
NP-hard on instances with `λ_2 >= eps/4`, so YES outputs have ratio at least
`1/4`. If UGC holds on loop-free regular instances, the same holds on loop-free
regular instances with `λ_2 >= eps/3`. The gate of (K1) is therefore sharp up
to the constant factor `4 X(eps)`: spectral expansion at ratio `Θ(1)` costs a
reduction nothing, and only ratio `X(s)` kills it. This is the shape of
AKKSTV's Theorem 2.6 (quoted in the citation route), reproved here with explicit
constants and without their soundness loss.

**(K3) Expanding world at low completeness.** For every `eps > 0` there is `l`
such that it is NP-hard to tell a linear unique game over `F_2^l` with
`opt >= (1−eps)/4` from one with `opt <= eps`, on instances whose constraint
graph has `λ_2 >= 3/8`. So spectral expanders are unconditionally hard at
completeness `1/4` and easy near completeness `1`. What separates genuine UG
hardness from the expanding world lives only in the completeness regime
`1 − opt > λ_2 / X(s)`.

**(K4) SSE sources sit outside the expanding world automatically.** A weighted
graph with a set `S` of volume fraction `μ in (0,1)` and expansion
`Φ(S) = w(E(S, V∖S))/vol(S) <= η` has `λ_2 <= η/(1−μ)`. So YES instances of
`Gap-Small-Set-Expansion(η, δ)` on regular graphs never have `λ_2 > η/(1−δ)`.
The route `ugc-from-small-set-expansion-hypothesis` needs no extra separating
step against this world at its source. For UG-on-small-set-expanders
formulations, (K1) adds that regular loop-free YES instances must expand small
sets while keeping `λ_2 <= X(s)(1 − opt)`, the noisy-cube shape.

*Survivors (not killed).*

* (S1) YES outputs whose constraint graphs are not regular or carry loops. The
  import is used only where its quoted proof applies.
* (S2) Outputs at ratio `λ_2/(1 − opt) < X(s)`. This includes all instances
  produced by (K2) at `c = Θ(eps)`.
* (S3) Every 2-to-1, 2-to-2 or rich outer hole. AKKSTV rounds permutation
  constraints only. The gate constrains the final unique game emitted by the
  inner test, not the outer game.
