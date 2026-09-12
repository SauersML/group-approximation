---
rg: 2
id: osin-non-mf-from-general-bounded-exponent
kind: route
title: Osin's quotient is an infinite finitely generated bounded-exponent group
target: osin-periodic-quotient-is-non-mf
requires:
  - infinite-fg-bounded-exponent-groups-are-non-mf
  - osin-torsion-universal-theory-separator
---

Instantiation. From `osin-torsion-universal-theory-separator`, the group
`Gbar = G/G^n` is

* **finitely generated**, being a quotient of the finitely presented `G`;
* of **exponent dividing `n`**, because `G^n` is a verbal, hence normal,
  subgroup and the quotient by it kills every `n`-th power;
* **infinite**, which is the content of the construction (the separator would
  be vacuous otherwise, since a finite group satisfies `(OS2)`).

So `infinite-fg-bounded-exponent-groups-are-non-mf` applies directly and
`Gbar` is not MF.

This route uses none of the analytic content of Osin's separator -- only the
three structural facts above. The separator's own statement `(OS2)` is what
the *other* route into this target consumes.
