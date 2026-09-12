---
rg: 2
id: formalizable-strict-pairs-certify-non-linear-soficity
kind: claim
title: A group carrying a formalizable strict automaton over a prime-power alphabet is not linear sofic in that characteristic
distinct_from:
  formal-polynomial-strict-pairs-need-unstable-linearization: that concludes bijectivity of formal pairs from direct finiteness; this reads it contrapositively and converts a formal strict pair into non-linear-soficity through the stable finiteness of linear sofic group algebras.
  linear-sofic-group-algebra-is-stably-finite: that is the passage from linear soficity to stable finiteness; this feeds that passage one new source of stable-finiteness failures, nonlinear formal strict pairs, not only one-sided inverse matrices.
  non-linear-sofic-group: that is the open root asking for some non-linear-sofic group; this names a sufficient certificate, a formalizable strict automaton, without supplying one.
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `p` be prime and `G` a group. If some strict automaton `tau` on `(F_p^n)^G` has a left inverse
`sigma` such that the pair is formalizable, possibly after adding identity tracks, then `F_p[G]` is not
stably finite. So `G` is not `F`-linear sofic for any field `F` of characteristic `p`.

**Payoff.** Any formalizable strict pair, on any group, would close `non-linear-sofic-group`. On `R^x`
over `F_2` it would refute `binary-leavitt-unit-group-is-f2-linear-sofic`. So stable formalizability
(`prime-field-left-inverse-pairs-are-stably-formalizable`) turns every Gottschalk counterexample over a
`p`-power alphabet into a non-linear-sofic group in characteristic `p`.

Proof: Section 8 of the artifact.
