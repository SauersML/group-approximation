---
rg: 2
id: stw99-problem-i-via-non-pathological-dimension
kind: route
title: Reduce Problem I to non-pathology of II_1 AW*-factor dimension functions (a finite weighted-cover lower bound)
target: stw99-problem-i-quasitraces-are-traces
requires:
  - stw99-ii1-awstar-dimension-is-non-pathological
  - stw99-quasitrace-minorant-zero-one-law
  - stw01-kaplansky-2q-pedersen-retract-equivalence
---

**Derivation.**

- If every `II_1` AW*-factor has cover mass `S_M(1) >= delta > 0`, then every such
  factor is W* (`stw99-quasitrace-minorant-zero-one-law`).
- By Gow's Theorem A (`stw01-kaplansky-2q-pedersen-retract-equivalence`), every
  bounded quasitrace is then a trace.

**Converse.** Problem I makes every `II_1` AW*-factor W*, and then
`S_M(1) = 1`. So this is an equivalence. The reduced statement is a one-sided
linear inequality with an arbitrary constant, so it is the formally weakest
known form. See artifact §4 for the constraints on violating covers.
