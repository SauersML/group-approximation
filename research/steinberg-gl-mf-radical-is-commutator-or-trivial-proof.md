---
rg: 2
id: steinberg-gl-mf-radical-is-commutator-or-trivial-proof
kind: route
title: Conjunction of the purely infinite K_1 classification and LEF of general linear groups over exactly matricial rings
target: steinberg-gl-mf-radical-is-commutator-or-trivial
requires:
  - purely-infinite-steinberg-gl-max-mf-quotient-is-k1
  - exactly-matricial-rings-have-lef-general-linear-groups
artifacts:
  - research/artifacts/un-k1-homology-2026-09-13-part1.md
---

**(1)** is the displayed equality of `purely-infinite-steinberg-gl-max-mf-quotient-is-k1`.

**(2)** `R` is countable by Step 1 of `purely-infinite-steinberg-gl-max-mf-quotient-is-k1-proof`, which uses only
second countability, compact unit space and countable `k`. So `exactly-matricial-rings-have-lef-general-linear-groups`
applies: `GL_n(R)` is LEF, and every LEF group is MF. Hence `GL_n(R)` embeds in an MF group, and the identity map is
an injective homomorphism to an MF group, so `Rad_MF(GL_n(R)) = 1`.

**Mutual exclusion.** An exactly matricial ring is stably finite: `∏_ω M_d(F)` is stably finite, since
`M_m(∏_ω M_d(F)) = ∏_ω M_(md)(F)` and one-sided invertibility passes to ω-almost every coordinate, where matrices
over a field are directly finite. Stable finiteness passes to unital subrings. Under (PI), Step 3 of the
compressibility proof gives `a, b` with `a^* a = b^* b = 1_X` and `a a^*`, `b b^*` orthogonal. Then `a a^* ≠ 1_X`,
so `a^* a = 1 ≠ a a^*`, and `R` is not directly finite.
