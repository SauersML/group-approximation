---
rg: 2
id: low-label-threshold-rank-reductions-cannot-prove-ugc
kind: claim
title: A deterministic eigen-free list rounding solves every unique game of value >= 1-eps whose label-extended walk has at most R eigenvalues above 1-800eps, to value 0.84-eps in time poly(Z) exp(O(R log R)), so reductions whose YES outputs have such low label-extended threshold rank cannot prove UGC unless P = NP
distinct_from:
  unique-games-gap-admits-polynomial-time-algorithm: that is the open refutation form of UGC for all instances; this solves only low label-extended threshold rank YES instances and turns that into an obstruction on reductions.
  unique-games-conjecture: that is the open hardness statement; this neither proves nor refutes it, it names a necessary property of the YES outputs of any reduction proving it.
  affine-ug-easy-on-certifiably-hypercontractive-graphs: that is an SoS algorithm for affine games on certified hypercontractive constraint graphs; this is a spectral list rounding for arbitrary permutations whose hypothesis is on the label-extended walk, not on the constraint graph.
  affine-ug-easy-on-globally-hypercontractive-graphs: that rounds affine games on globally hypercontractive graphs; this needs no group structure and no hypercontractivity, only few label-extended eigenvalues near 1.
  sticky-cylinder-gadget-compositions-cannot-prove-sseh: that kills SSE reductions at the NO case by a combinatorial invariant; this kills UG reductions at the YES case by a spectral invariant.
  galois-unique-game-value-is-transversal-expansion: that computes values of symmetric Cayley-lift games; this rounds arbitrary games with low label-extended threshold rank.
  small-set-expansion-hypothesis: that is the open SSE hardness statement; this concerns unique games and only records the high-threshold-rank survivors it motivates.
artifacts:
  - experiments/ugc-label-rank-kill-2026-09-17/check_label_rank_kill.py
---

**ESTABLISHED.** Elementary and self-contained, in the Turing (bit) model, with
no numerical linear algebra import. Proof: `low-label-threshold-rank-kill-proof`.

*Setting.* A unique game `U` has vertices `V` (`|V| = N`), alphabet `[k]`, and
positive integer weighted edges `e = (u, v, w_e, sigma_e)` with `u != v` and
`sigma_e` a permutation of `[k]`. A labeling `x` satisfies `e` if
`x_v = sigma_e(x_u)`. `val(x)` is the satisfied weight fraction. `Z` is the bit
size of `U`. Put `deg(u) = sum_(e at u) w_e`, `W = sum_e w_e`,
`pi(u) = deg(u) / 2W`. The **label-extended walk** on `V x [k]` is
`A_L((u,a),(v,b)) = sum_(e between u, v) (w_e / deg(u)) 1[b = sigma_e^(u->v)(a)]`.
It is stochastic and self-adjoint in `L2(pi_L)`, `pi_L(u,a) = pi(u)`, so its
eigenvalues are real. Write `rank_theta(A_L)` for the number of eigenvalues
`>= theta`, with multiplicity.

**Theorem.**

1. *(List rounding, eigen-free.)* There is a deterministic algorithm with inputs
   `U`, `eps in (0, 1/800]` and a cutoff `R*`. It either stops with "rank above
   `R*`", or outputs a labeling. It runs in time
   `poly(Z, 1/eps) (4 sqrt(2R* + 1)/0.09 + 2)^(2R*)`, which is
   `poly(Z, 1/eps) exp(O(R* log(R* + 1)))`.
   - If some labeling has `val(x) >= 1 - eps` and `rank_(1-800eps)(A_L) <= R*`,
     it outputs a labeling of value `>= 1 - eps - 0.16`.
   - If it stops with "rank above `R*`", then `rank_(1-800eps)(A_L) > R*`.

   The algorithm computes `P = ((I + A_L)/2)^t` exactly in rationals, selects
   columns greedily by `pi_L`-Gram--Schmidt until every residual is tiny, and
   enumerates a grid on the span, rounding each grid point by per-vertex argmax.
   No eigenvalue or eigenvector is ever computed.
2. *(Twisted trace certificate.)* `Tr(A_L^(2t)) <= k Tr(A^(2t))` for the
   constraint-graph walk `A`, hence `rank_theta(A_L) <= k Tr(A^(2t)) / theta^(2t)`
   for `theta > 0`. If `eps <= 1/1600` and `A` has at most `r0` eigenvalues of
   absolute value `> 1 - gamma`, then
   `rank_(1-800eps)(A_L) <= k (r0 + 1) exp(3200 eps ceil(log N / 2gamma))`,
   which is `k (r0 + 1) N^(O(eps/gamma))`. So with this cutoff, Theorem 1 runs
   in time `poly(Z) exp(O~(k (r0 + 1) N^(O(eps/gamma))))`, which is
   subexponential when `k (r0 + 1) = N^(o(1))` and `eps/gamma` is small.
3. *(Class kill.)* Let `Red` be a polynomial-time reduction from 3SAT to
   `Gap-UG[1 - eps, s]` with `eps <= 1/800` and `s < 0.84 - eps`. Let `Z` be the
   output size.
   - If every YES output has `rank_(1-800eps)(A_L) <= c log Z / log log Z`, then
     `P = NP`.
   - If every YES output has `rank <= (log Z)^c`, then `NP` is contained in
     quasi-polynomial time.
   - Assume ETH and let `Z <= n^A` on `n`-variable formulas. Then for every
     `alpha < 1/A`, infinitely many YES outputs have
     `rank_(1-800eps)(A_L) > Z^alpha`.

   No soundness property of `Red` is used.

**What dies, and where.** Every NP-hardness proof of `unique-games-conjecture`
is a reduction with completeness `1 - eps` and soundness `s -> 0`. It dies at
its **completeness case**, before any soundness analysis is reached, whenever
its YES outputs have label-extended threshold rank `O(log Z / log log Z)` at
`1 - 800 eps`, unless `P = NP`.

*The invariant* is `rank_(1-800eps)(A_L)`, the number of label-extended
eigenvalues within `800 eps` of 1. It ignores the permutations except through
the spectrum, and it ignores alphabet, gadget and soundness.

*The step.* The completing labeling `x` has indicator `f` with
`<f, A_L f> = val(x)`. At least `99%` of the mass of `f` lies in the span of the
eigenvalues of `(I + A_L)/2` above `1 - 50 eps`, which lie within `0.01` of
the greedy span. There a grid point within `0.2` of `f` rounds to value
`>= val(x) - 4(0.2)^2`.

Theorem 2 bounds the invariant by the constraint graph alone. With Theorem 3,
a reduction whose constraint graphs have `r0` eigenvalues above `1 - gamma` in
absolute value needs `k (r0 + 1) exp(3200 eps ceil(log N / 2gamma))` to exceed
`c log Z / log log Z` (for `eps <= 1/1600`), for every `c` unless `P = NP`.
For context only, not used in any proof: Arora--Barak--Steurer give a
subexponential algorithm in general, recorded in the Attempts of
`unique-games-gap-admits-polynomial-time-algorithm`.

**Sharpness.** The kill is tied to completeness near 1 and cannot reach
completeness `1/2`, consistent with `unique-games-hard-at-completeness-one-half`.
The mass bound `||f_lo||^2 <= (1 - <f,Bf>) / (1 - theta)` has
`<f,Bf> = (1 + val)/2 = 3/4`. For `theta >= 0`, where `B` has its whole
spectrum, the bound is at least `1/4`. So it only places `f` within `0.5` of
the span, and the rounding loss `4 ||g - f||^2` can reach `1`, which swamps the
gap.

**Survivors.** These are exactly the reductions whose YES outputs carry
`omega(log Z / log log Z)` label-extended eigenvalues near 1:

- **(S1)** long-code, short-code and noisy-cube fibre compositions, whose
  gadget walks have many eigenvalues `1 - O(eps)` per fibre;
- **(S2)** constraint graphs that are small-set expanders with many
  eigenvalues near 1, the BGHMRS graphs recorded in
  `small-set-expansion-hypothesis`.

The replay script checks the Rayleigh identity, the mass bound, the rounding
lemma, the twisted trace inequality, the greedy stopping bound `m <= 2R` and
end-to-end grid values on planted instances, in floats with moderate `tau`.

DERIVATION low-label-threshold-rank-kill-proof
