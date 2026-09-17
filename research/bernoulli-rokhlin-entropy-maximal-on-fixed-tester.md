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
  - research/artifacts/orbit-relation-bernoulli-entropy-2026-09-17.md
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
* **Orbit-relation reframing (a-gs-pull-11, 2026-09-17).**
  `bernoulli-extension-entropy-anti-monotone-in-subrelations` gives
  `h^Rok_U(A^U) = ε_{R_U}(A)`. This is the relative entropy of the Bernoulli extension
  of the orbit relation of `U ↷ [0,1]^U`, computable with any generating group of
  `[R_U]`. The target is therefore one relational statement:
  `ε_{R_U}(A, uniform) = log |A|`. `ε` is anti-monotone in subrelations and full on
  every amenable subrelation. So lower bounds cannot come from subrelations; that
  class is killed. They can only come from a super-relation. The transfer of
  maximality to `U` through a weakly minimal free action of a certified-maximal group
  whose orbit relation contains a free ergodic `U`-relation dies at the seed step:
  certified groups come from sofic seeds, and such an ambient relation would be
  sofic. This part is a remark, since it assumes Elek–Lippner, which is not imported.
  Artifact: `research/artifacts/orbit-relation-bernoulli-entropy-2026-09-17.md`,
  Section 7.
