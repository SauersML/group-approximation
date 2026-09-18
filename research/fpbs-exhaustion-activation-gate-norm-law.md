---
rg: 2
id: fpbs-exhaustion-activation-gate-norm-law
kind: claim
title: Along every exhaustion, the activation gate fails at the birth of every connected invariant spine below p_{2->2}, whether or not the family collapses; each volume costs a fixed mass on its own density window, giving a log-log law in general and a log law for decorrelated spines
distinct_from:
  fpbs-volume-uniform-activation-gate-log-law: that proves the log law only for gates holding uniformly over all finite volumes, using two-edge test volumes that no exhaustion contains; this proves failure along every exhaustion, from the norm of the spine-augmented kernel of each exhaustion volume
  fpbs-spine-increment-activation-gate: its Corollary 3 derives failure along every exhaustion only for collapse families, by contradiction with inf T_t > 0; this needs no property of omega_t at all, only a connected invariant spine born from nothing and a Bernoulli L2 window, and gives a rate
---

**ESTABLISHED (class-killing obstruction; exhaustion version of the log law).**
Proof in `fpbs-exhaustion-activation-gate-norm-law-proof`.

**Setting.** As in `fpbs-volume-uniform-activation-gate-log-law`. `G = Cay(Gamma,S)`
with degree `d`. `(Z_r)_{r in [t_0,t_1]}` is a label-independent environment
satisfying (E1) invariance, (E2) connected and infinite (or empty) and
(E3) continuous density `m(r) = P(o in V(Z_r))`, with `Z_{t_0} = ∅` and
`m(t_1) > 0`. `X^Lambda_r`, `beta^Lambda_r`, `S_r`, `D^A_{s,t}` are as in
`fpbs-annealed-pivotal-factorization-off-spine-bridges`. Additionally:

* **(H_B) Bernoulli L2 window.** `t_1 < p_{2->2}`, so
  `B = ||T^Bern_{t_1}||_{2->2} < infinity`. With `t_0 = p_c` this needs
  `p_c < p_{2->2}`, which Hutchcroft (arXiv:1904.05804) relates to critical
  L2 boundedness.

An exhaustion is `Lambda_1 ⊆ Lambda_2 ⊆ ...`, finite, with union `E`;
`W_j = V(Lambda_j)`. The gate (AG) along it with an atomless finite measure
`kappa_A` is `D^{A,Lambda_j}_{s,t} <= kappa_A((s,t]) X^{Lambda_j}_t J X^{Lambda_j}_t`
for all `j`, `t_0 <= s < t <= t_1`.

For finite `W` put `sigma_r(W) = ||S_r|_W||_{2->2}` and
`lambda_r(W) = <1_W, S_r 1_W> / |W|`.

**Theorem 1 (per-volume norm law).** If the gate holds in one volume
`Lambda` (with `W = V(Lambda)`), then for all `s < t`,

```text
d ( kappa_A((s,t]) + 2(t-s) )  >=  1/(B + B^2 sigma_s(W))  -  1/max(1, lambda_t(W)),
```

and always `m(r)^2 |W| <= lambda_r(W) <= sigma_r(W) <= m(r) |W|`.

**Theorem 2 (density windows).** Put `A = 2(B + B^2)` and
`c_0 = 1/(2 d (B + B^2))`. If the gate holds in `Lambda`, then

```text
kappa_A((s,t]) >= c_0 - 2(t-s)    whenever  m(s) <= 1/|W|  and  m(t) >= sqrt(A/|W|).
```

So each volume charges a fixed mass `c_0` to the density window
`[1/|W|, sqrt(A/|W|)]`, which moves to `0` as `|W| -> infinity`.

**Corollary 3 (every exhaustion, every born spine).** Along every
exhaustion, no finite atomless `kappa_A` satisfies (AG) on `[t_0,t_1]`.
Indeed, with the birth time `s* = max{r : m(r) = 0}` (which is `< t_1`),
`kappa_A((s*,t]) = infinity` for every `t in (s*, t_1]`. The same holds for
(AG*) and for the full gate. Nothing about `omega_t` is used: not collapse,
not uniqueness, not `inf T_t > 0`.

**Theorem 4 (rates).** Let the exhaustion have growth ratio
`|W_{j+1}| <= D |W_j|` (balls: `D = d`), and `a = A D`.

* **(log-log law, every spine).** If `m(t) <= 1/|W_1|`, then
  `kappa_A((s,t]) >= c_0 floor( log_2( log(a/m(s)) / log(a/m(t)) ) ) - 2(t-s)`.
* **(log law, decorrelated spines).** Suppose (Dec): there are `L` and `C_D >= 1`
  with `P(x, y in V(Z_r)) <= C_D m(r)^2` whenever `d_G(x,y) > L`. Put
  `K = sqrt(2 A C_D D)`. If `m(t) <= min(1/(2|B_L|), 1/sqrt(2 C_D |W_1|))`, then
  `kappa_A((s,t]) >= c_0 floor( log(m(t)/m(s)) / log K ) - 2(t-s)`.

For an arbitrary exhaustion the count of disjoint windows replaces the
floor: the mass on `(s,t]` is at least `c_0` times the number of volume
scales whose windows fit disjointly in `[m(s), m(t)]`.

**What this kills.** Corollary 3 of `fpbs-spine-increment-activation-gate`
reads the failure of (AG) as a trace of collapse. It is not: (AG) fails along
every exhaustion for every connected invariant spine born from `∅` on a graph
with `p_c < p_{2->2}`, including spine families whose `omega_t` is far from
unique. The gate therefore cannot separate collapse from non-collapse. Any
input implying (AG) along some exhaustion already implies that no connected
label-independent invariant spine is born at `t_0`. That is a restatement of
the product structure of Bernoulli percolation, not an estimate.
The quantitative loss is also located: in volume `W_j` the spine-augmented norm
passes from `O(1)` to `>= A` while the density moves from `1/|W_j|` to
`sqrt(A/|W_j|)` (generic) or by a fixed factor near `|W_j|^{-1/2}` (decorrelated).
This answers the open question of `fpbs-volume-uniform-activation-gate-log-law`:
along an exhaustion the law survives, with mass of order the number of volume
scales between `m(s)` and `m(t)`. A sparse exhaustion lowers the rate but not the
divergence.

**What is not decided.** Whether these rates are sharp. An upper bound would
require verifying (AG) entrywise, which Theorems 1-4 do not address. It is
also open whether the log-log rate can be improved to a log rate without
(Dec).
