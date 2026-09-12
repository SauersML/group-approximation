---
rg: 2
id: thompson-v-sofic-iff-not-permutation-stable-proof
kind: route
title: Fixed-point characters of almost actions of V are rigid, and weak local stability forces LEF
target: thompson-v-sofic-iff-not-permutation-stable
requires:
  - thompson-v-character-simplex
  - thompson-v-not-lef
artifacts:
  - research/artifacts/thompson-v-soficity-stability-and-full-groups-2026-09-12.md
---

Full proof: Section 2 of the artifact. Numbering follows the claim.

**Definitional implications.** Bradford's Remark 1.5 gives `2 => 3`, `2 => 4`, `3 => 5` and `4 => 5`.

**`5 => 1`.** A sofic, weakly locally stable group is LEF (Bradford, Lemma 2.15, immediate from
the definitions). `V` is not LEF by `thompson-v-not-lef`.

**`1 => 2`.** Let `phi_n` be an almost-homomorphism, and fix a nonprincipal ultrafilter `omega`.
Put `chi(g) = lim_omega |Fix(phi_n(g))| / k_n`.
- **`chi` is a character.** `phi_n(e)` is close to the identity, so `chi(e) = 1`. `chi` is a
  class function by bi-invariance of the Hamming metric. It is positive definite by the
  permutation identity
  `sum c_i conj(c_j) |Fix(sigma_j^-1 sigma_i)| = sum_(x,y) |sum_i c_i [sigma_i x = y]|^2`,
  whose error term is `o(k_n)`.
- **Rigidity.** By `thompson-v-character-simplex`, `chi = t tau_reg + (1-t) tau_triv`.
- **Amplification.** If `t > 0`, coordinatewise tensor powers `phi_n^(m)` on `[k_n]^m` have defect
  at most `m` times larger and fixed-point fractions raised to the power `m`. A diagonal sequence
  is then a separating almost-homomorphism, and `V` is sofic.
- **Conclusion.** Under (1), `t = 0` along every ultrafilter, so `d(phi_n(g), id) -> 0` for every
  `g`, and the trivial homomorphisms witness stability.

No property (T), no finite quotient and no IRS classification is used. The same argument covers
every finitely generated non-LEF group whose extreme characters are only `tau_reg` and `tau_triv`.
