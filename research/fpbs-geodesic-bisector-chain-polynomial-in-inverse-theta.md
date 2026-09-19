---
rg: 2
id: fpbs-geodesic-bisector-chain-polynomial-in-inverse-theta
kind: claim
title: The bisector-split chain bound K <= C theta^{-gamma} with finite gamma extends from the straight path to every monotone (geodesic) path, and to lambda-quasi-geodesics with gamma = O(lambda); on the straight path the gate gamma < 36/5 reduces exactly to one critical-percolation inequality P_{1/2}(D_n) >= pi(n)^beta with beta < 18/5 for the pattern-free box event D_n, which has a linear-time pinch-wall face criterion; critical Monte Carlo to n = 2048 gives beta_eff ≈ 2.4 (zeta ≈ 0.25, with no upward drift), i.e. gamma ≈ 4.8
distinct_from:
  fpbs-bisector-chain-is-polynomial-in-inverse-theta: that proves the polynomial bound on the straight path only, and leaves the gate as a numerical statement about the near-critical infinite-volume event; this proves the bound for every monotone path, and reduces the gate rigorously (Proposition C) to a single inequality at p = 1/2 for a finite-box event
  fpbs-planar-spine-multirun-decorrelation-by-dual-circuits: that gives the chain K <= q(S^-)q(S^+)/(Theta^- Theta^+) with Theta bounded by Harris, exponential in the correlation length; this bounds Theta on geodesic paths polynomially in 1/theta
artifacts:
  - research/fpbs-geodesic-bisector-chain-polynomial-in-inverse-theta-proof.md
  - experiments/fpbs-shield-exponent-2026-09-18/phi_fast.c
  - experiments/fpbs-shield-exponent-2026-09-18/pool.py
  - experiments/fpbs-shield-exponent-2026-09-18/run_all.sh
  - experiments/fpbs-shield-exponent-2026-09-18/results.txt
---

**ESTABLISHED:** Theorems A and B and Proposition C (with Corollary C.1).
They use near-critical RSW and exponential decay as black boxes, as
`fpbs-bisector-chain-is-polynomial-in-inverse-theta` does. **OPEN:** the
critical inequality (H). The proof is in
`fpbs-geodesic-bisector-chain-polynomial-in-inverse-theta-proof`, and the
numerics are in `experiments/fpbs-shield-exponent-2026-09-18/`.

**Setting.** As in `fpbs-bisector-chain-is-polynomial-in-inverse-theta`.

* Bernoulli(`p'`) bond percolation on `Z^2`, with `p' > 1/2`,
  `theta = theta(p')` and `L = L(p')`.
* The path `x_0, ..., x_n` has distinct vertices and a cut edge
  `x_k x_{k+1}`.
* `L` and `R` are the dual edges closer to `U^-` and to `U^+` in the
  Euclidean bisector sense.
* The chain is `K(S) <= q(S^-) q(S^+) / (Theta^-(S) Theta^+(S))`.

**Theorem A (geodesic paths).** Suppose the path is monotone, that is,
`|x_i - x_j|_1 = |i - j|`. Then `Theta^±(S) >= c L^{-kappa_1}` for every
pattern, split, length and `p'`, with

    kappa_1 = 64 log_2(1/(c(4)^4 c(12))) + 5 log_2(1/c(4)),

where `c(a)` are the critical RSW constants. Hence
`K(S) <= C theta^{-2 kappa_1/alpha}`.

* The construction uses 64 linked primal circuits per dyadic scale in
  boxes of half-width `t/8` around path vertices at path distance `t` from
  the cut. Those boxes lie inside the bisector half (Lemma A.1), and an
  escape to infinity finishes the chain.
* For `λ`-quasi-geodesics the same proof gives an exponent `O(λ)`.
* Hairpins are not covered: Lemma A.1 fails there.

**Theorem B (pinch-wall criterion).** In the box `B_n` with wired
boundary, let `I` be the wired cluster.

* The walls are the edges with both ends in `I`, and the diagonals of
  plaquettes whose opposite corners both lie in `I`.
* `D_n` fails iff some `v = (a,0) notin I`, `-n < a <= 0`, lies in a face
  of the wall arrangement that meets a plaquette with centre abscissa
  `>= 1/2`.
* `D_n` is decided in `O(n^2)` time. The linear-time evaluator has 0
  mismatches against the block algorithm of w14.

**Proposition C.** `Phi(p') := P_{p'}(D^-(U^-_∞)) >= c · P_{1/2}(D_{4 C_0 L(p')})`.
The proof glues three increasing events by FKG: the box event, an RSW
circuit, and a subcritical-dual event with no large dual circuits.

**Corollary C.1.** Suppose

    (H)   P_{1/2}(D_n) >= c · pi(n)^β   for some β < 18/5.

Then `K(S) <= C theta^{-2β}` on the straight path, so the gate
`gamma < 36/5` holds. At the triangular-lattice exponents, (H) reads
`zeta < 3/8`.

**Numerics (critical, `p = 1/2`).**

* Samples: 5,900 to `n = 1024`, of which 1,100 go to `n = 2048`, with
  nested boxes `n = 8..N`.
* The local slopes `-log_2 P(D_{2n} | D_n)` lie between `0.21` and
  `0.27` over `n = 16..2048`, each with errors of about `0.01-0.02`, and
  show no upward drift. Their weighted mean over `n >= 64` is `0.251(6)`.
  The one-arm calibration slope is `0.097-0.108`, against the exact
  `5/48 = 0.104`.
* So `zeta ≈ 0.25` and `β_eff ≈ 2.4`, against the threshold `3.6`. The
  value `3/8` is excluded at every scale by more than 7 standard errors.
* The value is consistent with `1/4`. It is inconsistent with `1/3`, with
  `5/48` and with the backbone value `0.357`.

**Refuted along the way.** "Two open half-plane arms at `0` imply `D`" is
false: a closed pocket below the axis that opens to the right is a
counterexample (§3.1 of the proof). So there is no one-line comparison
with the half-plane one-arm exponent.

**Next step.** Prove (H). Two routes are open:

* On the triangular lattice: compute the CLE_6 wedge exponent of the
  event "no loop of diameter `>= ε` meets both the negative real axis and
  the imaginary axis" (proof §3.4). The conjectured value is `1/4`, which
  would give `gamma = 24/5`.
* Directly on `Z^2`: find an arm event of exponent `< (18/5)` times the
  one-arm exponent that implies `D_n`.
