---
rg: 2
id: positive-rokhlin-entropy-makes-leavitt-units-surjunctive-proof
kind: route
title: Embed the square of the Leavitt unit group by corners and apply the self-copy dichotomy
target: positive-rokhlin-entropy-makes-leavitt-units-surjunctive
requires:
  - rokhlin-supremum-dichotomy-with-centralized-self-copies
  - positive-rokhlin-entropy-action-gives-positive-supremum
  - infinite-rokhlin-supremum-forces-surjunctivity
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
---

Complete proof in Section 2 of the artifact.

* **Corners.** From `t_i s_j = delta_ij` and `s_0 t_0 + s_1 t_1 = 1`, the maps `iota_0(a) = s_0 a t_0 + s_1 t_1` and `iota_1(b) = s_0 t_0 + s_1 b t_1` are injective homomorphisms `U -> U`. Their images commute and meet trivially, so `U x U <= U`.
* **Large finite subgroups.** For `|u| = |v| = n`, the elements `s_u t_v` are matrix units whose diagonal units sum to `1`. They give a unital embedding `M_(2^n)(F_2) -> L`, which is injective because the matrix algebra is simple. Hence `GL_(2^n)(F_2) <= U`.
* **Dichotomy.** The self-copy corollary of `rokhlin-supremum-dichotomy-with-centralized-self-copies` gives (1).
* **Equivalences.**
  * POS iff `h^Rok_sup > 0`: Seward's Corollary 7.7, recorded as `positive-rokhlin-entropy-action-gives-positive-supremum`.
  * INF gives RBS, surjunctivity and direct finiteness: `infinite-rokhlin-supremum-forces-surjunctivity`.
  * RBS gives POS through the Bernoulli 2-shift.
