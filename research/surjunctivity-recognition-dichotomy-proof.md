---
rg: 2
id: surjunctivity-recognition-dichotomy-proof
kind: route
title: Seed the hereditary switch and Adian--Rabin with the canonical rectangle host
target: surjunctivity-recognition-dichotomy
requires:
  - surjunctivity-recognition-has-a-pi2-upper-bound
  - surjunctivity-is-axiomatized-by-rectangle-clauses
  - arbitrary-forbidden-seed-hereditary-property-switch
  - surjunctivity-passes-to-subgroups
artifacts:
  - research/artifacts/gottschalk-rectangle-clauses-and-recognition-2026-09-12.md
---

Section 4 of the artifact.

- **(A)** The sets are full or empty.
- **(B1)** A counterexample realizes strict data `D`, so the finitely presented
  `P(D)` realizes them and is not surjunctive (axiomatization, Corollary 1.5).
- **(B2)** Surjunctivity is hereditary, holds for the trivial group, and fails for
  the finitely presented seed `P(D)`. Clause (P5) of
  `arbitrary-forbidden-seed-hereditary-property-switch` makes the positive
  enumerated set `Pi^0_2`-hard and the negative one `Sigma^0_2`-hard. The upper
  bound supplies membership.
- **(B3)** "Surjunctive" is a Markov property of finite presentations: the trivial
  group has it, and `P(D)` embeds in no surjunctive group. Adian--Rabin gives a
  computable `w -> P_w`, from the words of a finitely presented group with
  `Sigma^0_1`-complete word problem, with `P_w` trivial when `w = 1` and containing
  `P(D)` when `w != 1`. So `SURJ_fp` is `Sigma^0_1`-hard and `NONSURJ_fp` is
  `Pi^0_1`-hard. Neither is at the first level on the other side.
- **Equivalences.** (i) gives (ii) to (v) by (B). Under (A) the sets are full or
  empty, and a computable set is not `Pi^0_2`-complete.
