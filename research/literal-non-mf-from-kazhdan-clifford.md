---
rg: 2
id: literal-non-mf-from-kazhdan-clifford
kind: route
title: Instantiate the Kazhdan--Clifford construction at the literal base
target: literal-central-mark-corona-invisible
requires: [kazhdan-clifford-non-mf-construction, literal-kazhdan-clifford-inputs]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralNonMFEndpoint.lean
  - GroupApproximation/Sofic/LiteralSixGenerator.lean
---

## Why sufficient

Substitution of the literal base, doubling self-embedding, and `v_1` into the
general construction gives exactly the displayed presentation and marked
word.  The explicit Clifford-linear witness proves `w != 1`; the presentation
relations make `w` central, and the general construction kills it in every
corona model.  The Tietze identities express `v_2` and `v_3` through the six
remaining generators.  Restricting a hypothetical MF embedding of either
group C-star algebra to canonical group unitaries would contradict the mark's
universal invisibility.
