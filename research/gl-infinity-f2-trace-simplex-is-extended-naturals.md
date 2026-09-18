---
rg: 2
id: gl-infinity-f2-trace-simplex-is-extended-naturals
kind: claim
title: The trace simplex of GL(infinity,2) is the probability simplex on the extended naturals, and the Jacobson non-symbol CE locus is a closed additive semigroup
distinct_from:
  gl-infinity-f2-extreme-characters-are-rank-powers: that is the imported list of extreme characters; this proves that the list is closed, gives the affine homeomorphism of all traces with Prob({0,...,infinity}), and draws the consequence for EL_n(J).
  leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity: that proves that one CE character of EL_n(J) seeing L forces hyperlinearity (JH1); this shows that the CE indices m, for which the zero extension of 2^(-m rank) is CE, form a closed additive semigroup of {1,...,infinity}, and that each finite index forces all its multiples.
  ce-characters-closed-multiplicative-semigroup: that is the general closure of the CE locus under products and limits; this computes that locus inside the explicit countable list.
artifacts:
  - research/gl-infinity-f2-trace-simplex-is-extended-naturals-proof.md
---

**ESTABLISHED** ([[gl-infinity-f2-trace-simplex-is-extended-naturals-proof]]).

**Notation.**
* `N̄ = {0,1,2,...,∞}` is the one-point compactification of `N`. It is an additive semigroup with
  `∞ + x = ∞`.
* `sigma_m(g) = 2^(-m rank(g-1))` on `L ≅ GL(∞,2)`, with `sigma_∞ = δ_e`.
* `Prob(N̄)` carries the weak* topology, and `Tr(L)` carries the pointwise topology.

**Theorem.**
1. **(Bauer simplex.)** The map `Phi(mu) = sum_m mu({m}) sigma_m` is an affine homeomorphism from `Prob(N̄)`
   onto `Tr(L)`.
   * `Ch(L) = {sigma_m}` is closed and homeomorphic to `N̄`.
   * `sigma_(m_j) -> sigma_m` pointwise iff `m_j -> m` in `N̄`.
   * Every pointwise limit of traces (in particular of characters) of `L` is `Phi` of the weak* limit of
     their measures.
2. **(Products.)** `sigma_m sigma_l = sigma_(m+l)` and `Phi(mu) Phi(nu) = Phi(mu * nu)`, where `*` is
   convolution on the semigroup `N̄`.
3. **(Detection by one transvection.)** Let `t` be a transvection and let `tau = Phi(mu)`.
   * `tau(t) = sum_(m<∞) mu_m 2^(-m)`.
   * `tau(t) = 1` iff `tau = 1`.
   * `tau(t) = 0` iff `tau = δ_e`.
4. **(Jacobson elementary groups.)** Let `n >= 2`, `E = EL_n(J)` and `L = L_n`.
   * The characters of `E` not factoring through the symbol are exactly `e sigma_m`, `1 <= m <= ∞`, and
     `e sigma_∞ = δ_e`.
   * Put `S = {m in [1,∞] : e sigma_m in CE(E)}`. Then `S` is closed in `N̄`, `S + S ⊆ S`, and `∞ in S` iff
     `E` is hyperlinear.
   * If `S` contains a finite `m`, then `∞ in S`.
   * Hence **`E` is hyperlinear iff `S` is nonempty.** Either `S ⊆ {∞}`, or `S` contains `∞` and every
     sufficiently large multiple of `d = gcd(S ∩ N)`.

**What this does for the open hole.**
* The survivor class "pointwise limits" of `jacobson-mirror-exact-trace-part-is-multiplicative`
  (swarm-0917-w9-w9-nh-pull) asked for exactly this list, in need `bounty=56` on
  `agent-leavitt-not-bcs-negative-root-corner`.
* Part 1 gives that list, and shows that limits of rank characters are rank characters with the limiting
  index.
* Part 4 compresses the last hole, hyperlinearity of `EL_20(J)`, to the question whether one explicit
  character `e sigma_m`, the Haar fixed-point character `phi_m` of (JH2), is CE for **some** `m`.
* A CE proof for one finite `m` (for example the Haar character `phi_1`) proves that `EL_20(J)` is
  hyperlinear.
* Proving that `EL_20(J)` is not hyperlinear requires excluding every `m`, including `m = ∞`.
