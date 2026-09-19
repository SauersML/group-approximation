---
rg: 2
id: fpbs-bisector-chain-is-polynomial-in-inverse-theta
kind: claim
title: On the straight path the bisector-split chain bounds the Z^2 spine decorrelation by K(S) <= 1/(Phi^- Phi^+) for every pattern at once, where Phi^- is the probability of one pattern-free event (no dual-open circuit leaving the left half-plane surrounds a point of the negative axis); nested left-half-plane primal circuits give Phi^± >= c L(p')^{-kappa}, so K <= C theta^{-gamma} with gamma finite, replacing the source's theta^{-c xi}; critical Monte Carlo (n <= 256) gives effective zeta between 0.24 and 0.31(5) against the gate value 3/8, i.e. gamma ≈ 4.6-5.9 < 36/5
distinct_from:
  fpbs-planar-spine-multirun-decorrelation-by-dual-circuits: that proves K <= 1/(Theta^- Theta^+) and bounds Theta^± by Harris over the vertices near the cut, which gives a constant of order theta^{-c xi}, exponential in the correlation length; this bounds Theta^± below by one pattern-free event and bounds that event by one RSW factor per dyadic scale, which gives a constant polynomial in 1/theta, uniformly in the pattern
  fpbs-bisector-split-chain-caps-at-inverse-theta-squared: that proves the chain can never reach C/theta, because Theta^± are at most theta/p' on two-run patterns and at most (1-c_0)^{#scales} on dyadic patterns; this proves the matching lower bound Theta^± >= c L^{-kappa} for all patterns, so the chain's output is exactly polynomial in L(p'), and measures the exponent against the activation gate
artifacts:
  - research/fpbs-bisector-chain-is-polynomial-in-inverse-theta-proof.md
  - experiments/fpbs-finger-shield-exponent-2026-09-18/theta_chain.c
  - experiments/fpbs-finger-shield-exponent-2026-09-18/run_all.sh
  - experiments/fpbs-finger-shield-exponent-2026-09-18/results.txt
---

**ESTABLISHED (Theorems 1-3; Theorem 3 uses near-critical RSW as a black
box, as Theorem B of `fpbs-bisector-split-chain-caps-at-inverse-theta-squared`
does). OPEN: the value of the exponent (Conjecture 4, numerical).** Proof in
`fpbs-bisector-chain-is-polynomial-in-inverse-theta-proof`. Numerics in
`experiments/fpbs-finger-shield-exponent-2026-09-18/`.

**Setting.** As in `fpbs-bisector-split-chain-caps-at-inverse-theta-squared`.
Bernoulli(`p'`) bond percolation on `Z^2`, with `p' > 1/2`,
`theta = theta(p')` and correlation length `L = L(p')`. The path is straight,
the cut is `e_k = (0,0)(1,0)`, `U^- = {(a,0) : a <= 0}` and
`U^+ = {(a,0) : a >= 1}`. The bisector sets are `L` (dual midpoints with
first coordinate `< 1/2`) and `R` (first coordinate `> 1/2`). The chain of
`fpbs-planar-spine-multirun-decorrelation-by-dual-circuits` is

```text
K(S) = q(S)/(q(S^-) q(S^+)) <= 1/(Theta^-(S) Theta^+(S)),   Theta^-(S) = P_{S^-}(D^-(V(S^-))),
```

where `D^-(W)` is the event that no dual-open circuit not contained in `L`
surrounds a vertex of `W`. `Theta^+` is defined symmetrically with `R`.

**Theorem 1 (pattern-free reduction).** Let `Phi^- = P(D^-(U^-))`, with no
edge declared. Define `Phi^+` symmetrically; by reflection `Phi^+ = Phi^-`.
Then for every pattern `S` and every split,

```text
Theta^±(S) >= Phi^±,   hence   K(S) <= 1/(Phi^- Phi^+) = 1/Phi^2 .
```

So the chain's worst case over all patterns is governed by one event with
no pattern in it. The w13 obstruction shows this is essentially the true
behaviour: on dyadic patterns `Theta^±` decays by a constant factor per
dyadic scale up to `L`.

**Theorem 2 (exact description of `D^-(U^-)`).** Let `G_N` be the union
of the dual-open blocks (2-connected components and bridges) that contain
an edge not in `L`. A vertex `v` is surrounded by a dual-open circuit not
contained in `L` if and only if `v` lies in a bounded face of `G_N`. So
`D^-(U^-)` says that no point of the negative axis lies in a bounded face
of `G_N`. On a box proxy this can be decided exactly by one block
decomposition and one flood fill (`theta_chain.c`). The same test works
with a declared pattern. For the pattern `{(-1,0)(0,0)}` it reproduced
Theorem A of the w13 node sample by sample (`D^-` equals the run reaching
`∂B_n`), with 0 mismatches in 4000 samples at `n = 8, 20`.

**Theorem 3 (polynomial lower bound).** There are absolute constants
`c, kappa > 0` such that for all `p' in (1/2, 1)`,

```text
Phi^± >= c L(p')^{-kappa},   hence   K(S) <= C L(p')^{2 kappa} <= C' theta(p')^{-gamma_0}
```

for every pattern and every split on the straight path, with
`gamma_0 = 2 kappa / alpha` and `alpha` the RSW exponent in `pi(n) <= n^{-alpha}`.
The mechanism is a family of nested primal-open circuits, one per dyadic
scale, lying in the left half-plane and each surrounding a dyadic stretch
of the negative axis. Consecutive circuits intersect, so they form one
unbounded cluster. Any dual-open circuit around an axis point is then
trapped inside one of these circuits, and so lies in `L`. Each scale up to
`L` costs one RSW constant, and scales beyond `L` cost a convergent
product.

This replaces the source node's `theta^{-c xi}`, which is super-polynomial
since `xi ≍ L`, by `theta^{-gamma_0}`. Together with the w13 upper bound
`Theta^- <= (1-c_0)^{#scales}`, it shows that the chain's uniform output
is *exactly polynomial* in `L(p')`: it is `L^{2 zeta_*}` with
`0 < zeta_* <= zeta_Phi`.

**Conjecture 4 (numerical: the chain clears the activation gate).**
`Phi(p') ≍ L(p')^{-zeta}` with `zeta < 3/8`. Given that, `theta ≍ L^{-5/48}`
yields `K(S) <= C theta^{-gamma}` with `gamma = 96 zeta/5 < 36/5`, uniformly
over all patterns. This is the "minimum goal for the activation gate"
(`Theta^± >= c theta^{gamma/2}`, `gamma < 36/5`) on the straight path.

Critical box proxies at `p' = 1/2` (target `∂[-n,n]^2`; standard errors from
a 20-batch jackknife) give the following. `PI` is the one-arm proxy
`P(0 <-> ∂B_n)` and calibrates the method: its local slopes are 0.10-0.11,
against the exact `5/48 = 0.104`.

```text
  n     Phi            PI         local slope of Phi   of PI    of Phi/PI
 16   0.5937(24)   0.7097(25)
 32   0.5027(36)   0.6569(36)        0.240            0.111      0.129
 64   0.4279(40)   0.6147(46)        0.233            0.096      0.137
128   0.3693(62)   0.5745(74)        0.213            0.098      0.115
256   0.2983(84)   0.5303(91)        0.31(5)          0.115      0.19(5)
```

The `n = 256` row pools six independent 500-sample runs. The quantity
that matters for the gate is `zeta_Phi / (5/48)`, which must stay below
`3.6`. Two estimates:

* The ratio of fitted slopes over `n = 16..256` is `0.243/0.103 = 2.35`.
* The ratio `log Phi / log PI` is `1.52, 1.64, 1.75, 1.80, 1.91`.

The least-squares slope of `Phi` over `n = 16..256` is `0.243`, so
`gamma ≈ 4.7`. The local slope from 128 to 256 is `0.31 ± 0.05`, which
gives `gamma ≈ 5.9`. That is still below `7.2`, but it is only about 1.4
standard errors under the gate value `0.375`, and the local slopes are not
clearly converged.

So the numerics favour the gate, but they are not decisive. That is why
this is recorded as a conjecture.

On the dyadic and alternating patterns (`DY2`, `DY4`, `ALT`), `Theta^-`
sits above `Phi` at every `n`, as Theorem 1 requires. Its slopes
(0.16-0.19) exceed `5/48`, which matches the w13 finger loss.

Near-critical runs at `n = 128`, where `L(p')` is much smaller than `n`,
give `(Phi, PI) = (0.859, 0.888)` at `p' = 0.56` and `(0.931, 0.937)` at
`p' = 0.60`. At `p' = 0.66` and `0.75`, `Phi = PI` to three digits. So
`Phi` and `theta` saturate together, as Theorem 3 predicts.

**What this settles, and what it leaves.**

* *The brief's shared-arm Step 1 is not needed for the gate.* The
  existing bisector chain, with Step 4 replaced by Theorem 1, already has
  polynomial output (Theorem 3). Its exponent is numerically 4.6-5.9,
  below 7.2 (Conjecture 4). The shared-arm Step 1 (arm separation) is needed only for the sharp
  `K <= C/theta`, which by the w13 obstruction no bisector-type chain can
  give.
* *The remaining rigorous step is one exponent inequality,
  `zeta_Phi < 3/8`, for one pattern-free event.* RSW constants alone
  cannot give it: Theorem 3 pays about `log_2(1/c_RSW)` bits per scale,
  while the gate allows only `3/8 - 5/48 ≈ 0.27` bits per scale beyond the
  one-arm cost. The natural routes are an SLE_6/CLE_6 computation on the
  triangular lattice (the event is conformally invariant: no CLE_6 loop
  that surrounds a point of the negative axis meets the right half-plane),
  or a comparison of `D^-(U^-)` with an arm event whose exponent is known
  and below 3/8. Candidates are the polychromatic two-arm exponent `1/4`
  and the half-plane one-arm exponent `1/3`.
* *Scope.* The theorems are stated for the straight path, the w13 setting.
  For a geodesic (monotone) path, the same construction with circuits in
  tubes of width `d/4` around the path stretches `[d, 2d]` should give
  Theorem 3. Hairpins are not touched.
