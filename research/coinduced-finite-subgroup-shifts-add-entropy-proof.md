---
rg: 2
id: coinduced-finite-subgroup-shifts-add-entropy-proof
kind: route
title: Transcribe Seward's common-factor-plus-Ornstein construction to co-induced F-spaces, then tune one free orbit
target: coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli
requires:
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
artifacts:
  - research/artifacts/bernoulli-negative-coinduced-ornstein-2026-09-12.md
  - research/artifacts/bernoulli-negative-induced-absorption-2026-09-12.md
---

**Theorem C** is Section 2 of `research/artifacts/bernoulli-negative-coinduced-ornstein-2026-09-12.md`,
Steps 1–6:
1. `theta_i` keeps labels in `P` and writes `*` elsewhere. Both push forward to the same product measure `mu`.
2. `G` acts freely and mixingly on the factor. At a coset fixed by `s`, a label must be `*`, because `P` is
   free. At moved cosets, two independent labels agree with probability below `1`.
3. `V` picks one root per `*`-coset, and `T` is aperiodic in the pseudo full group of `E ∩ V×V`
   (Jackson–Kechris–Louveau Lem. 3.25, as in Seward).
4. The complements `A_i = Y_i \ P` have equal entropy. Ornstein's theorem for `Z`, with finite or infinite
   entropy (Ornstein 1970, [17, 18] of Seward), gives `zeta: A_1^Z -> A_2^Z`.
5. `pi` recodes the distinguished-root labels along `T`-rows by `zeta`. It extends to all roots through the
   co-induced relation `x(tf) = f^-1 . x(t)`.
6. Over each fibre of the common factor, the root labels are i.i.d. `alpha_i`. `pi` maps rows to `zeta` of
   rows, and the same construction with `zeta^-1` inverts it.

**Corollary D** is Section 1 of `research/artifacts/bernoulli-negative-induced-absorption-2026-09-12.md`:
- Lemma T realizes any entropy above a floor with prescribed atoms.
- `K` is replaced, by Theorem 1.1, with an entropy-equal `K'` having atoms `1 - delta` and `eps`. The orbit of
  `(y_0, k*)`, with `k*` equal to `k_1` at `1_F` and `k_0` elsewhere, is free with point mass
  `c = nu(y_0) eps (1-delta)^(|F|-1)`.
- `M` has atoms `b` of mass `1 - 3 eps` and `a` of mass `c/(1-3eps)^(|F|-1)`, and entropy `h*`. The pattern
  `a` at `1_F`, `b` elsewhere has a free orbit of the same point mass.
- The entropies agree: `H(Y) + |F| H(K) = |F| h*`. Theorem C gives `Coind(Y) × K'^G ≅ M^G`, and Theorem 1.1
  finishes.

**Trust surface.** Ornstein's theorem for `Z` and the Jackson–Kechris–Louveau lemma, both used by Seward
exactly as here. The transcription of Seward's Section 3 is unreviewed.
