---
rg: 2
id: regular-table-defects-are-short-edge-h1-trivial
kind: claim
title: Regular-table defects are trivial in the short-edge H1 coefficient system
distinct_from:
  short-edge-gauge-torsor-h1-vanishes: that theorem asks for quantitative bounded control after local triviality is assumed; this claim asks for the existence of the local zero-cochain itself.
  ambient-h1-triviality-need-not-be-short-edge-local: that firewall shows ambient compatibility does not imply a geometrically local zero-cochain.
  regular-table-local-h1-restates-spherical-gauge: that established firewall proves this claim is equivalent at the qualitative asymptotic level to the spherical local-gauge target, rather than an independent intermediate lemma.
---

**OPEN; ROOT-STRENGTH RESTATEMENT.**  For every fixed finite
regular-character multiplication table `T`, the relation defects produced
by sufficiently tight simultaneous spherical shadow matchings define the
trivial class in the nonabelian `H^1` obstruction set whose coefficients
are the geometrically local permutations of the cloud, modulo the already
charged exceptional roots.

Operationally, triviality means that there are local source corrections
`c_s` satisfying every gauge equation

```text
c_k = delta_(g,h,k)
      (sigma_h^(-1)c_g sigma_h)c_h
```

modulo `o(N)` roots.  By
[[regular-table-local-h1-restates-spherical-gauge]], this is exactly the
qualitative asymptotic conclusion of
[[spherical-short-holonomies-admit-local-gauge]], and diagonalization
recovers its finite tolerance form.

Thus this node cannot serve as an independent prerequisite for the
spherical gauge theorem.  A genuine advance must construct the zero-cochain
from stronger checkable data, such as explicit bounded defect-word fillers,
rather than assume that the desired local class vanishes.
