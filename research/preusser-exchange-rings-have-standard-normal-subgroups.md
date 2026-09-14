---
rg: 2
id: preusser-exchange-rings-have-standard-normal-subgroups
kind: claim
title: Preusser (arXiv:1912.11386) — over an exchange ring, subgroups of GL_n normalized by E_n are sandwiched between level subgroups for n ≥ 3
distinct_from:
  vaserstein-local-stable-range-normal-subgroups: that is Vaserstein's sandwich theorem under a local stable-range hypothesis; this is Preusser's sandwich theorem for exchange rings, with no stable-range hypothesis.
artifacts:
  - research/artifacts/sk-stable-rank-a-shortcut-2026-09-13-part1.md
---

**ESTABLISHED (literature import).** R. Preusser, "On general linear groups over exchange rings",
arXiv:1912.11386v1 (23 Dec 2019).

- **Theorem 3.** "Suppose that R is an exchange ring and n ≥ 3. Let H be a subgroup of GL_n(R). Then H is
  normalised by E_n(R) iff there is an ideal I ⊴ R such that E_n(R,I) ⊆ H ⊆ C_n(R,I). Moreover, the ideal I is
  uniquely determined."
- Here "C_n(R,I) := φ^{-1}(Center(GL_n(R/I)))" is the full congruence subgroup of level `I`, where `φ` is induced by
  `R → R/I`.
- Theorem 1 of the same paper: for an exchange ring `R` and an ideal `I`, `E_n(R,I)` is normal in `GL_n(R)`.

An exchange ring is one where, for every `x`, there is an idempotent `e ∈ xR` with `1 − e ∈ (1−x)R` (Nicholson).
Examples: semiperfect, von Neumann regular, and purely infinite simple rings. The non-MF manuscript uses this theorem
for `L_(F_2)(1,2)^×`.
