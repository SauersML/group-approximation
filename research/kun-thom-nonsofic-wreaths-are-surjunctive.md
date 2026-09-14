---
rg: 2
id: kun-thom-nonsofic-wreaths-are-surjunctive
kind: claim
title: The Kun--Thom nonsofic generalized wreath products over residually finite Kazhdan bases are surjunctive
distinct_from:
  kun-thom-wreath-stably-finite: that is Kaplansky stable finiteness of the same groups over every field, a linear statement; this is Gottschalk surjunctivity for arbitrary nonlinear automata.
  kun-thom-nonsofic-wreath: that imports the nonsoficity of these groups; this proves they satisfy the dynamical conclusion soficity is normally used to supply.
artifacts:
  - research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md
---

Let `Gamma <= G` be infranormal and not normal, with both groups Kazhdan and
`G` residually finite. The explicit family is Theorem E of Kun--Thom,
arXiv:2608.06222:

```text
Gamma = EL_r(F_q[x_1,...,x_d]),
G     = EL_r(F_q[x_1^(+-1),...,x_d^(+-1)]) semidirect SL_d(Z),     r,d >= 3.
```

Then

```text
W = (Z/2Z) wr_(G/Gamma) G = (direct_sum_(G/Gamma) Z/2Z) semidirect G
```

is surjunctive: every injective finite-alphabet cellular automaton over `W`
is surjective.

**Derivation.**
* `G` is residually finite, hence surjunctive.
* `rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive`, applied with the
  finite lamp `Z/2Z` and the coset action on `G/Gamma`, makes `W` surjunctive.

No sofic approximation of `W` or of the coset action is used, and none
exists by `kun-thom-nonsofic-wreath`.

These groups are therefore not Gottschalk counterexamples. A counterexample
built from the (T)-compression nonsoficity mechanism must leave the
permutational-wreath form over a surjunctive base. The Leavitt unit group,
twisted lamps and amalgams remain open.
