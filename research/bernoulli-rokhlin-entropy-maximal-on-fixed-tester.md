---
rg: 2
id: bernoulli-rokhlin-entropy-maximal-on-fixed-tester
kind: claim
title: Uniform Bernoulli shifts over the fixed Gottschalk tester host have maximal Rokhlin entropy
distinct_from:
  bernoulli-rokhlin-entropy-maximal-for-every-group: that quantifies over all countable groups; this is the single host U, and two recorded routes make them equivalent.
  fixed-gottschalk-test-group-is-surjunctive: that is surjunctivity of U; this is a measurable entropy statement about U that implies it.
  tester-host-has-positive-rokhlin-entropy-action: that asks for a positive-entropy action of the restricted sum Gamma_U of copies of U x Sym_fin(N), which settles Gottschalk through the self-copy dichotomy; this asks for maximal Bernoulli entropy on U itself, equivalent to maximality for every group by subgroup and colimit closure.
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

**OPEN.** Let `U` be the two-generator finitely presented host of
`universal-all-group-subgroup-colimit-class-tester`. For every finite alphabet
`A` with `|A| >= 2`, `h^Rok_U(A^U, uniform) = log |A|`.

This implies surjunctivity of `U`
(`fixed-tester-surjunctive-via-rokhlin-entropy`), and so Gottschalk's conjecture.
It is equivalent to `bernoulli-rokhlin-entropy-maximal-for-every-group`. One
direction specializes. The other uses closure under subgroups and under directed
colimits.

## Attempts

* **Soficity of `U`.** Soficity would suffice, but finite presentation supplies no
  finite models, as the fixed tester node already records. Not available.
* **Finitary witnesses.** By `bernoulli-rokhlin-deficit-has-a-finitary-witness`, a
  failure is one configuration of translates in `U` whose information about a
  coordinate exceeds its own entropy. No configuration has been tested, and no
  inequality is proved for the incidence patterns of `U`.
