---
rg: 2
id: galois-games-round-through-free-subgroups
kind: claim
title: A Galois unique game has value >= 1 - mu(G minus H) for every H acting freely on G/K, and an SDP value 1-eps yields such H from <= log2 k irreducibles of dimension-weighted cost
distinct_from:
  elementary-abelian-galois-games-round-with-linear-loss: that is the elementary abelian case with Bochner and Fourier inversion and the Khot--Vishnoi tightness; this is the rounding principle over every finite group, a representation-theoretic proof, and the abelian corollary for every exponent.
  galois-unique-game-value-is-transversal-expansion: that computes the value, the perfect case and the SDP; this constructs labelings from free subgroups and from SDP certificates.
artifacts:
  - research/artifacts/ugc-galois-games-part2-2026-09-12.md
---

**ESTABLISHED.** Notation of `galois-unique-game-value-is-transversal-expansion`.

1. **Duality.** For `H <= G`, the following are equivalent: `H` acts freely
   on `G/K`; `K` acts freely on `G/H`; `H cap x K x^-1 = {e}` for all `x`.
2. **Free-subgroup rounding.** For every such `H`,
   `val Gal(G,K,mu) >= 1 - mu(G \ H)`. The witness is `g -> g^-1 H`, followed
   by one representative per `K`-orbit on `G/H`. The perfect-completeness
   criterion is the case `mu(G \ H) = 0`.
3. **Irreducible-kernel rounding.** Let `G` have exponent `m` and `mu` be
   conjugation-invariant, with `SDP >= 1 - eps`. Then some irreducibles
   `rho_1..rho_t` satisfy `t <= log_2 k`, `lambda_(rho_i) >= 1 - 3 eps`, and
   `K cap (ker rho_1 cap ... cap ker rho_t) = {e}`. With `H` that common kernel,
   `val >= 1 - 3 eps (d_1 + ... + d_t)/(1 - cos(2 pi/m))`. The proof: on the
   good kernels' intersection with `K`, the certificate has `Re phi >= 1/3`,
   yet it must vanish on `K \ {e}`. Markov in Hilbert--Schmidt norm then bounds
   `Pr[rho(s) != I]`.
4. **Every finite abelian group.** `val >= 1 - 3 eps log_2 k/(1 - cos(2 pi/m))`.
   Some dependence on `m` is necessary: the odd cycle, as `Z_(2n)`, loses
   `sqrt(eps)`.

The dimension factor is where large representations escape. For `S_N`
transposition noise, the standard representation certifies `1 - O(eps)` but is
useless for kernel rounding, while the point stabilizer is a good free subgroup
when `K` is semiregular. Whether free subgroups always suffice at bounded
exponent is `free-subgroup-rounding-is-universal-at-bounded-exponent`.

This constrains symmetric integrality-gap constructions only. It neither
proves nor refutes `unique-games-conjecture`.

DERIVATION galois-games-round-through-free-subgroups-proof
