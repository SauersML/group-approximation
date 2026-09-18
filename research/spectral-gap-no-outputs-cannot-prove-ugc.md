---
rg: 2
id: spectral-gap-no-outputs-cannot-prove-ugc
kind: claim
title: The basic unique-games SDP satisfies val >= 1 - 768 eps/gamma - 14 eps - 18 r^(2/3) eps^(1/3) whenever the constraint walk has at most r eigenvalues above 1-gamma, for every alphabet; so a UGC reduction whose NO outputs have at most c(1-delta)^(3/2) eps^(-1/2) eigenvalues above 1 - C eps/(1-delta) implies P = NP
distinct_from:
  low-label-threshold-rank-reductions-cannot-prove-ugc: that kills reductions at the YES case through the label-extended threshold rank at super-logarithmic scale by exact list rounding; this kills them at the NO case through the constraint-graph spectrum alone, by the degree-2 SDP, and needs no rank bound on the label-extended walk.
  unique-games-gap-admits-polynomial-time-algorithm: that is the open refutation form for all instances; this decides only instances whose NO side has few eigenvalues near 1.
  unique-games-conjecture: that is the open hardness statement; this names a necessary spectral property of the NO outputs of any reduction proving it.
  affine-ug-easy-on-certifiably-hypercontractive-graphs: that needs affine constraints and a hypercontractivity certificate; this works for arbitrary permutations and uses only r eigenvalues.
  affine-ug-easy-on-globally-hypercontractive-graphs: that needs affine games and global hypercontractivity; this needs only a threshold-rank bound on the constraint walk.
  spread-support-overlap-forces-non-expanding-small-sets: that is a combinatorial NO-side constraint on SSE-type outputs; this is a spectral NO-side constraint on arbitrary UG outputs.
  small-set-expansion-hypothesis: that is the open SSE hardness hypothesis; this only identifies its high-threshold-rank expanders as the surviving NO outputs.
artifacts:
  - experiments/ugc-spectral-no-kill-2026-09-17/check_spectral_no_kill.py
---

**ESTABLISHED.** Proof: `spectral-gap-no-output-kill-proof`, with the solver
import `sdp-fixed-precision-solvable-gls`.

*Setting.* A unique game `U` has vertices `V` (`|V| = N`, none isolated),
alphabet `[k]`, and positive integer weighted edges `e = (u, v, w_e, sigma_e)`
with `u != v`. A labeling `x` satisfies `e` if `x_v = sigma_e(x_u)`, and
`val(U)` is the largest satisfied weight fraction. Put `W = sum_e w_e`,
`deg(u) = sum_(e at u) w_e`, `pi(u) = deg(u)/2W`, and let `A` be the constraint
walk `A(u,v) = w(u,v)/deg(u)`. It is self-adjoint in `L2(pi)` with real
eigenvalues `1 = lambda_1 >= lambda_2 >= ... >= lambda_N >= -1`. The **basic
SDP** is

```text
sdp(U) = max E_e sum_a <u_a, v_(sigma_e a)>
  over vectors u_a (u in V, a in [k]) with <u_a, u_b> = 0 (a != b),
  sum_a ||u_a||^2 = 1,
```

where `E_e` weights edge `e` by `w_e/W`. It has no triangle inequalities, and
`sdp(U) >= val(U)`.

**Theorem.**

1. *(Rounding.)* Let `r >= 1` and `gamma > 0`, and suppose `A` has at most `r`
   eigenvalues `> 1 - gamma`. Put `eps = 1 - sdp(U)`. Then
   `val(U) >= 1 - 768 eps/gamma - 14 eps - 18 r^(2/3) eps^(1/3)`.
   If `r = 1`, the last term can be dropped:
   `val(U) >= 1 - 768 eps/gamma - 14 eps`.
   The same bounds hold with `eps` the deficit of any feasible vector solution.
   The alphabet size `k` does not appear.
2. *(Algorithm.)* Let `eps0, delta` be rational with `0 < eps0` and
   `0 <= delta < 1`. Suppose `r, gamma` satisfy
   `1536 eps0/gamma + 28 eps0 + 18 r^(2/3) (2 eps0)^(1/3) < 1 - delta`.
   Then there is a deterministic polynomial-time algorithm, uniform in `k`,
   that accepts every `U` with `val(U) >= 1 - eps0` and rejects every `U` with
   `val(U) <= delta` whose walk has at most `r` eigenvalues `> 1 - gamma`. It
   computes the SDP to additive precision `eps0/3` and thresholds at
   `1 - 1.5 eps0`. The eigenvalues are never computed.
3. *(Class kill.)* Let `Red` be a polynomial-time reduction from 3SAT to
   `Gap-UG[1 - eps0, delta]`. If every NO output has at most `r(Z)` eigenvalues
   above `1 - gamma` with `r, gamma` as in item 2 (they may depend on the output
   size `Z`), then `P = NP`. In particular, it suffices that
   `56 eps0 < 1 - delta`, `gamma >= 3072 eps0/(1 - delta - 56 eps0)` and
   `r < (1 - delta)^(3/2)/(216 sqrt(2 eps0))`. No completeness property of `Red`
   beyond `val >= 1 - eps0` is used.

**What dies, and where.** Every NP-hardness proof of `unique-games-conjecture`
maps unsatisfiable formulas to games of value `<= delta`. It dies at its
**soundness case**, before any gadget analysis, whenever the NO outputs have
at most `c (1-delta)^(3/2) eps0^(-1/2)` eigenvalues above `1 - C eps0/(1-delta)`.
This covers every alphabet size, every choice of permutations, and every
gadget.

*The invariant* is the threshold rank of the constraint walk at
`1 - Theta(eps0/(1-delta))`, at scale `eps0^(-1/2)`.

*The step.* On a NO output, if the SDP were `>= 1 - 2 eps0`, then the
fourth-tensor embedding `N(u) = sum_a ||u_a|| (u_a/||u_a||)^(x4)` would have
Dirichlet energy `<= 8 eps0`. Its part outside the top `r` eigenspaces would
have mass `<= 8 eps0/gamma`. A random grid of cell diameter `Delta` on the
`r`-dimensional projection cuts edges of weight `<= r sqrt(16 eps0)/Delta`.
Inside a cell, a root vertex propagates a consistent labeling through the
partial matchings `S_ac = <u_a/||u_a||, w_c/||w_c||>^2 > 1/2`, losing
`32 eta_u + 32 eta_v + 14 eps_e` per edge. The result is a labeling of value
`> delta`.

**Consistency.**

* At completeness `1/2` (`unique-games-hard-at-completeness-one-half`),
  `eps0 = 1/2` makes item 2's hypothesis false. Nothing is contradicted.
* Khot--Vishnoi noisy-cube instances with noise `eta` have SDP deficit of order
  `eta`. Their walks have eigenvalues `(1 - 2eta)^|S|`, so at
  `gamma = C eta` about `n^(C/2)` eigenvalues lie above `1 - gamma`. That grows
  with `n` and is far above `eta^(-1/2)`, as item 3 requires.
* No optimality of the constants or of the exponents `2/3, 1/3` is claimed.

**Survivors.** These are exactly the reductions whose NO outputs have many
constraint-graph eigenvalues within `O(eps0)` of 1:

- **(N1)** long-code, short-code and noisy-cube compositions. Their gadget walks
  carry polynomially many eigenvalues `1 - O(eps0)` per block.
- **(N2)** SSE constraint graphs with many near-1 eigenvalues (the BGHMRS graphs
  recorded in `small-set-expansion-hypothesis`).

Together with `low-label-threshold-rank-reductions-cannot-prove-ugc`, a UGC
reduction must carry high threshold rank on both sides:
`omega(log Z/log log Z)` label-extended eigenvalues near 1 on YES outputs, and
`Omega(eps0^(-1/2))` constraint eigenvalues within `O(eps0)` of 1 on NO outputs.

**Credit and context.** These are not used in the proof and were not re-read
here:

* The fourth-tensor propagation for `r = 1` is the idea of
  Arora--Khot--Kolla--Steurer--Tulsiani--Vishnoi (STOC 2008), "Unique games on
  expanding constraint graphs are easy". Makarychev--Makarychev refine it.
* Kolla, and Arora--Barak--Steurer, round low threshold rank in time
  exponential in the rank.
* What is new here is the self-contained version without triangle inequalities
  and with explicit constants: the random-grid rounding in polynomial time at
  rank `r`, and the conversion into a NO-side obstruction on reductions. A
  literature search for a prior polynomial-time rank-`r` statement of this form
  was not done.

The replay script checks, in floats:

* `s^4 >= 4s - 3`, the edge lemma, the deficit identity, and the matching
  bounds;
* the exact per-edge failure probability of root rounding against
  `40 eta_u + 24 eta_v + 14 eps_e`;
* the Dirichlet identities, the residual bound `E||R||^2 <= 4 eps/gamma`, and
  `E(PN) <= E(N)`;
* end-to-end grid-rounding values against item 1 on planted expander games,
  with the bound non-vacuous for `m <= 4`.

DERIVATION spectral-gap-no-output-kill-proof
