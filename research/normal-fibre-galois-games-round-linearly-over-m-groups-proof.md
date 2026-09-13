---
rg: 2
id: normal-fibre-galois-games-round-linearly-over-m-groups-proof
kind: route
title: Induced characters on class functions equal the inducing character's value; a halving chain of conjugated inducing kernels inside K
target: normal-fibre-galois-games-round-linearly-over-m-groups
requires: [galois-games-round-through-free-subgroups, galois-unique-game-value-is-transversal-expansion]
artifacts:
  - research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md
---

Complete proofs: Lemma 11, Lemma 12a and Theorem 12 of the artifact.

* **Induced certificates (Lemma 11).** By the induced character formula,
  `chi_rho(g)/d_rho = |G|^-1 sum_x chidot_sigma(x^-1 g x)/d_sigma` for
  `rho = Ind_H sigma`. Against a conjugation-invariant `mu` each `x` gives the
  same sum, so `lambda_rho = sum_(h in H) mu(h) chi_sigma(h)/d_sigma`. For a
  linear `theta`,
  `1 - lambda_rho = sum_g mu(g)(1 - Re thetadot(g)) >= (1 - cos(2 pi/m)) mu(G \ ker theta)`.
* **M-groups (Lemma 12a).** Let `G` be a `p`-group and `chi` faithful and
  non-linear. A maximal abelian normal `A` is self-centralizing. If
  `chi|_A` were homogeneous, `A` would be central, so `G = A`. Hence the inertia
  group of a constituent is proper, and the Clifford correspondence plus
  induction on `|G|` shows `chi` is monomial. Nilpotent groups are products of
  `p`-groups, and tensor products of induced characters are induced.
* **Good components.** The symmetric SDP formula of
  `galois-unique-game-value-is-transversal-expansion` supplies an admissible
  `phi`. Step (ii) of irreducible-kernel rounding in
  `galois-games-round-through-free-subgroups` gives
  `K cap (intersection of ker rho over good rho) = {e}`, where good means
  `w_rho > 0` and `lambda_rho >= 1 - 3 eps`.
* **Chain.** `ker Ind_H theta` is the intersection of the conjugates of
  `ker theta`. While `N_(i-1) = K cap L_1 cap ... cap L_(i-1)` is nontrivial,
  pick `a` in it, a good `rho` with `a notin ker rho`, and a conjugate `L_i` of
  its inducing kernel omitting `a`. The order drops by at least `q` each time,
  so `t <= log_q k`.
* **Cost and value.** Conjugation invariance and Lemma 11 give
  `mu(G \ L_i) <= 3 eps/(1 - cos(2 pi/m))`, and a union bound finishes. Since `K`
  is normal, `L cap K = {e}` means `L` meets every conjugate trivially, and
  free-subgroup rounding (part 2 of the required claim) bounds the value.
