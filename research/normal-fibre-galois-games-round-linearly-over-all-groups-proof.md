---
rg: 2
id: normal-fibre-galois-games-round-linearly-over-all-groups-proof
kind: route
title: Induce every good irreducible from a primitive representation, bound the primitive kernel's mass by the trace gap, and halve K along conjugates
target: normal-fibre-galois-games-round-linearly-over-all-groups
requires: [primitive-projective-representations-have-a-trace-gap, galois-games-round-through-free-subgroups, galois-unique-game-value-is-transversal-expansion]
artifacts:
  - research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md
  - research/artifacts/ugc-rounding-normal-fibres-part2-2026-09-13.md
---

Complete proofs: Lemma 11 and Theorem 12 of part 3, and Theorem 16 of part 4.

* **Certificate.** The symmetric SDP formula of
  `galois-unique-game-value-is-transversal-expansion` gives admissible `phi`.
  Step (ii) of irreducible-kernel rounding in
  `galois-games-round-through-free-subgroups` gives
  `K cap (intersection of ker rho over good rho) = {e}`, where good means
  `w_rho > 0` and `lambda_rho >= 1 - 3 eps`.
* **Primitive inducing data.** Take `H` minimal with `rho = Ind_H sigma`; then
  `sigma` is primitive. The induced character formula against
  conjugation-invariant `mu` gives
  `1 - lambda_rho = sum_g mu(g)(1 - Re chidot_sigma(g)/d_sigma)`. The summand is
  `1` off `H` and `0` on `ker sigma`. For `sigma(h) = zeta I` with `zeta != 1`,
  `zeta^m = 1` gives at least `1 - cos(2 pi/m)`. For non-scalar `sigma(h)`, the
  required trace gap for `H` gives at least `1 - gamma(H) >= 1 - gamma(G)`. So
  `mu(G \ ker sigma) <= 3 eps/c(G,m)`.
* **Chain.** `ker rho` is the intersection of the conjugates of `ker sigma`. While
  `K cap L_1 cap ... cap L_(i-1)` contains some `a != e`, pick a good `rho` with
  `a notin ker rho`, and a conjugate `L_i` of its primitive kernel omitting `a`.
  Orders drop by at least `q`, so there are at most `log_q k` steps.
* **Value.** A union bound and conjugation invariance give the mass bound. Since
  `K` is normal, `L cap K = {e}` makes `L` free on `G/K`, and free-subgroup
  rounding (part 2 of the required claim) bounds the value.
