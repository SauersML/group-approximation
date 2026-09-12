---
rg: 2
id: clifford-cover-nonsurjunctive-from-anti-half-df-failure
kind: route
title: A one-sided inverse in the anti-central Clifford skew ring refutes surjunctivity of the cover
target: kun-thom-clifford-cover-nonsurjunctive
requires:
  - clifford-cover-anti-half-skew-ring-not-directly-finite
  - clifford-cover-group-algebra-splits-into-wreath-and-skew-ring
  - stable-finiteness-failure-refutes-surjunctivity
artifacts:
  - research/artifacts/clifford-cover-surjunctivity-test-host-2026-09-12.md
---

- A pair `b a = 1 != a b` in `A_S`, padded with the unit of `F_3[W]`, is a one-sided inverse pair in
  `F_3[E_S]`.
- `stable-finiteness-failure-refutes-surjunctivity` turns it into an injective non-surjective linear
  automaton over `E_S`.
