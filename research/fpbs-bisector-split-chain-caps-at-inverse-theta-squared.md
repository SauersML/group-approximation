---
rg: 2
id: fpbs-bisector-split-chain-caps-at-inverse-theta-squared
kind: claim
title: The dual-circuit bisector-split chain for the Z^2 spine decorrelation K cannot reach K <= C/theta, whatever Step 4 (outermost circuit, RSW annuli) is used; on the adjacent two-run pattern of a straight path its best possible output is 1/(q(S^-)q(S^+)) >= p'^2/theta^2, and on sparse dyadic patterns it loses a factor >= L(p')^kappa from finger circuits; the loss is in Step 1, which discards the shared arm, while Monte Carlo puts the true K*theta near 0.8 on every tested pattern
distinct_from:
  fpbs-planar-spine-multirun-decorrelation-by-dual-circuits: that proves the chain K <= 1/(Theta^- Theta^+) with Theta >= prod max(theta, 1 - psi) and asks for an outermost-circuit refinement of Step 4 reaching C/theta; this proves no refinement of Step 4 can, because on explicit patterns Theta^± themselves are at most theta/p' (two-run) or (1-c_0)^{J_*} (dyadic), so the exact output of (3.1) is already above p'^2/theta^2, resp. L(p')^kappa
  fpbs-path-bridge-ratio-untilted-coverage-decorrelation: that proves the true K <= 2/theta on two-run patterns by a last-exit bound; this uses that bound to show the chain is off by at least p'^2/(2 theta) on the simplest two-run pattern, i.e. the chain is not sharp even where the answer is known
artifacts:
  - research/fpbs-bisector-split-chain-caps-at-inverse-theta-squared-proof.md
  - experiments/fpbs-dyadic-multirun-2026-09-18/dyadic.c
  - experiments/fpbs-dyadic-multirun-2026-09-18/run_all.sh
  - experiments/fpbs-dyadic-multirun-2026-09-18/results.txt
---

**ESTABLISHED (class-killing obstruction for the bisector-split chain;
Theorem A is elementary and complete, Theorem B uses near-critical RSW as
a black box).** Proof in
`fpbs-bisector-split-chain-caps-at-inverse-theta-squared-proof`.
Numerics: `experiments/fpbs-dyadic-multirun-2026-09-18/`.

**Setting.** As in `fpbs-planar-spine-multirun-decorrelation-by-dual-circuits`.
`omega` is Bernoulli(`p'`) bond percolation on `Z^2`, `p' > 1/2`,
`theta = theta(p')`. For a pattern `F` of path edges,
`P(F ⊆ Z) = p'^{|F|} q(F)`, where `q(F) = P_F(no dual-open circuit surrounds V(F))`.
The decorrelation constant at split `k` is `K(S) = q(S)/(q(S^-) q(S^+))`.
The *bisector-split chain* is Steps 1-3 of that node's proof. With `L`, `R`
the dual edges strictly closer to `U^-`, resp. `U^+`, it gives

```text
q(S) <= P_S(A^L) P_S(B^R)                                   (Step 1)
q(S^-) >= P_{S^-}(A^L) Theta^-,  Theta^- = P_{S^-}(D^-)        (Steps 2-3)
=>  K(S) <= 1 / (Theta^- Theta^+).                            (3.1)
```

Here `D^-` is the event that no dual-open circuit not contained in `L`
surrounds a vertex of `V(S^-)`. Step 4 of that node, and every refinement
of it (outermost-circuit decomposition, RSW circuits in dyadic annuli
around the cut, any sum of annulus contributions), is a *lower bound on
`Theta^±`*. So no Step 4 can make the chain's output smaller than the
exact value `1/(Theta^- Theta^+)`.

**Straight path.** `x_i = (i-k+1, 0)`, so the cut is `e_k = (0,0)(1,0)`,
`U^- = {x <= 0}` and `U^+ = {x >= 1}` on the axis. Then `L` is exactly the
set of dual edges whose midpoint has first coordinate `< 1/2`, and `R` the
set with first coordinate `> 1/2`.

**Theorem A (two-run pattern: the chain is exact and off by `1/theta`).**
On the straight path, let `S = {e_{k-1}, e_{k+1}}`. Then
`P_S(A^L) = P_S(B^R) = 1`, `Theta^± = q(S^±) <= theta/p'`, and Steps 1-3
hold with equality at the level of (3.1):

```text
1/(Theta^- Theta^+) = 1/(q(S^-) q(S^+)) >= p'^2 / theta^2,   while   K(S) <= 2/theta.
```

So the bisector-split chain, with *any* Step 4, cannot prove anything
better than `K <= p'^2/theta^2` on geodesic paths. It is off by a factor of
at least `p'^2/(2 theta)` on the simplest pattern where the true answer is
known (`fpbs-path-bridge-ratio-untilted-coverage-decorrelation`, Theorem 2).

*Mechanism.* Every dual circuit surrounding `(0,0)` crosses the positive
half-axis, at a dual edge with midpoint `(i+1/2, 0)`, `i >= 0`, which is not in
`L`. So `A^L` holds for free, Step 1 bounds `q(S)` by `1`, and all
the information that `S` must reach infinity, including the one arm that
`S^-` and `S^+` *share*, is thrown away. Steps 2-3 then divide by the full
cost `q(S^-) q(S^+) ~ theta^2` of two separate arms.

**Theorem B (sparse dyadic patterns: a multiscale loss).** Fix `b >= 4`.
On the straight path, let `S^-_J` consist of the edges `(-b^j,0)(-b^j+1,0)`
for `1 <= j <= J`, and let `S^+_J` be its mirror image under `x -> 1-x`. Let
`L(p')` be Kesten's characteristic length of the dual (subcritical) measure.
There are absolute constants `c_0 > 0` and `c_1` such that

```text
Theta^±(S_J) <= (1 - c_0)^{J_*},   J_* = #{ j <= J : 32 <= b^j <= c_1 L(p') }.
```

Hence the exact output of the chain on `S_J` is at least `(1-c_0)^{-2 J_*}`.
For `J` large this is at least `c L(p')^kappa` with
`kappa = 2 log(1/(1-c_0)) / log b > 0`. So it tends to infinity as
`p' -> 1/2`, even on patterns whose true `K` stays near `0.8/theta` (table
below).

*Mechanism.* In the tube around the polygon
`(-3r/2,-r/2) -> (-3r/2,r/2) -> (r,r/2) -> (r,r/4) -> (-r/2,r/4) -> (-r/2,-r/2)`,
with `r = b^j`, a dual-open "finger" circuit surrounds `(-b^j,0)`. It
passes over the cut into `{x > 1/2}`, so it is not in `L`, yet it does not
surround `(0,0)`. Near-critical RSW makes the tube circuit appear with
probability at least `c_0` at every scale `b^j <= c_1 L(p')`. The tubes for
different `j` are disjoint, so they are independent. Such circuits are
counted against `Theta^-` but cost nothing in the numerator bound of
Step 1, because they are not in `L`.

**Where the RSW sum fails.** This answers the lane's question. Placing
RSW circuits in dyadic annuli around the cut and summing annulus
contributions only ever lower-bounds `Theta^±`. Theorems A and B are *upper*
bounds on `Theta^±`, so they cap every such sum.

* Annuli around the cut contribute a factor `theta` to `Theta^-` that is
  never cancelled. Step 1 dropped the matching factor from the numerator:
  `A^L` does not see any circuit around the cut at any scale.
* Finger circuits around each run contribute a constant factor per
  dyadic scale.

The failure is **Step 1, not Step 4**. Any repair must keep in the
numerator bound a part of the shared-arm event `D^- ∩ D^+`, which the
product `P(A^L) P(B^R)` discards.

**Numerics (true `K`, not the chain).** The script is
`experiments/fpbs-dyadic-multirun-2026-09-18/dyadic.c`. It runs at `p = 1/2`
in the box `[-M,M]^2` with target `∂B_M`, the finite-size proxy for
`p' - 1/2 ~ M^{-3/4}`. The patterns are the dyadic patterns of Theorem B
with `j = 0..J-1`, so `J = 1` is the adjacent two-run pattern of Theorem
A. The proxy for `theta` is `P((0,0) <-> ∂B_M)`. Jackknife standard errors
use 20 batches. The full tables are in `results.txt`.

```text
 M   base  samples  theta_proxy |  J=1     J=2     J=3     J=4     J=5     (K*theta)
 32   2     20000    0.6557     | 0.8435  0.8192  0.8036  0.7938  0.7911
 64   2     40000    0.6187     | 0.8445  0.8215  0.8052  0.7949  0.7868
128   2     30000    0.5772     | 0.8463  0.8232  0.8054  0.7971  0.7914   (J=6: 0.7765)
128   4     30000    0.5747     | 0.8473  0.8339  0.8316                   (Theorem B's base)
                                  (se <= 0.005 for J <= 5)

Chain's exact output at J=1 (Theorem A: 1/(q(S^-) q(S^+))), same samples:
 M  | true K   chain    chain*theta   chain*theta^2
 32 | 1.2865   1.8420   1.208         0.7920
 64 | 1.3650   2.0856   1.290         0.7983
128 | 1.4661   2.4000   1.385         0.7996
```

The true `K*theta` stays in `[0.77, 0.85]` and is flat in `M`. It
*decreases* slightly as more dyadic scales are added. The chain's output
tracks `0.8/theta^2`: `chain*theta^2` is flat, while `chain*theta` grows,
exactly as Theorem A predicts. The chain's exact output grows at least
like `theta^{-2}` (Theorem A), and on the same patterns by a further
factor per scale (Theorem B). So the obstruction is to the method, not to
the statement: `K <= C/theta` on geodesic paths remains plausible and is
supported by the data.

**What this moves.** It closes the lane's step. The outermost-circuit and
RSW-annulus refinements of the bisector chain cannot give `C/theta`. The
chain also cannot give any bound that is uniform over dyadic patterns and
depends on `theta` alone with a constant independent of RSW constants,
because of the `L(p')^kappa` loss.

For the activation gate (`fpbs-spine-increment-activation-gate`), only a
polynomial bound is needed. With `theta ~ (p'-1/2)^{5/36}`,
`K <= C theta^{-gamma}` is integrable near `1/2` for every
`gamma < 36/5`. Theorem A's `theta^{-2}` is harmless for the gate. So the
chain is not dead for the gate. Whether it survives is decided by the
multiscale exponent in Theorem B against the gate threshold, and that is
a statement about `Theta^±` alone:

**Open (the strongest step left).** Prove
`Theta^±_k(S) >= c theta^{gamma/2}` uniformly over patterns on geodesic
paths, for some `gamma < 36/5`. Theorem B shows that the proof must pay
for finger circuits scale by scale. A per-scale cost
`Theta^- >= prod_{scales} (1 - c'_0)` with `(1-c'_0)^{-2} < b^{36 alpha /5}`,
where `alpha` is the exponent in `theta ~ L^{-alpha}`, would suffice. Separately,
the sharp `K <= C/theta` needs a new Step 1 that keeps one shared arm, for
example `q(S) <= C P(A^L_{<rho}) P(B^R_{<rho}) pi(rho, infinity)` at the pattern scale
`rho`, proved by arm separation (quasi-multiplicativity).

## Attempts

- w13-123 (flagship-2026-09-17): outermost-circuit / dyadic-RSW refinement
  of Step 4 toward `K <= C/theta`. Dead: Theorems A-B show the exact output
  `1/(Theta^- Theta^+)` of (3.1) is already `>= p'^2/theta^2`, resp.
  `>= L(p')^kappa`, so no Step 4 reaches `C/theta`. The loss is in Step 1.
