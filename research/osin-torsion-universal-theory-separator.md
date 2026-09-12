---
rg: 2
id: osin-torsion-universal-theory-separator
kind: claim
title: A finite universal sentence separates finite groups from finitely generated torsion groups
distinct_from:
  mf-universal-horn-obstruction: that quasi-identity is derived FROM this repository's established non-MF theorem and excludes MF groups; this is a classical group-theoretic separator between finite and torsion groups, proved with no analysis, and it is an INPUT rather than an output.
  mf-relation-closure: that organizes the MF radical of relations as a closure operator and names the semantic consequence operation; this is one concrete separating sentence in a different pair of classes.
artifacts:
  - research/artifacts/opnorm-burnside-dossier-2026-08-24.md
---

**Literature input.**  Osin, *On the universal theory of torsion and lacunary
hyperbolic groups*, arXiv:0903.3978, Groups Complexity Cryptology **1** (2009)
no. 2, 311--319, proves that the universal theory of torsion groups is
**properly** contained in the universal theory of finite groups, answering a
question of Dyson.

Concretely there is a finite universal sentence valid in every finite group
and refuted in some finitely generated torsion group. Written out, there are
a finitely presented

```text
G = <x_1,...,x_s | R_1,...,R_t>
```

containing a suitable free Burnside subgroup, an exponent `n`, and finitely
many words `W_1,...,W_q` in `F_s` such that, for the quotient
`Gbar = G/G^n`,

```text
W_1 != 1, ..., W_q != 1   in Gbar,                               (OS1)
```

while every finite group `H` satisfies the generalized quasi-identity

```text
R_1 = 1, ..., R_t = 1   ==>   W_j = 1 for some j.                (OS2)
```

Here `Gbar` is finitely generated (a quotient of the finitely presented `G`),
has exponent dividing `n` (`G^n` is verbal, hence normal, with quotient of
exponent dividing `n`), and is infinite -- that is the content of the
construction.

**Trust surface, stated exactly.**  The bibliographic data and the headline
theorem (proper containment of the two universal theories, answering Dyson)
were verified this session from the published record. The displayed shape
`(OS1)`--`(OS2)` -- the specific presentation, the passage to `G/G^n`, and the
infiniteness of `Gbar` -- is reported at the level of an external dossier and
was **not** re-derived from the paper here. Two scope points that a consumer
must respect:

* A universal sentence is in general only equivalent, after putting its
  negation in disjunctive normal form, to a **disjunctive** implication
  `(OS2)`; a single-conclusion Horn quasi-identity `... ==> W = 1` is a
  special case and is not automatic. Downstream statements are written for
  the disjunctive form.
* Osin's separator is a statement about **torsion** groups. Nothing in it
  asserts anything about MF, coronas, or operator norms, and it supplies no
  stability modulus. Everything analytic is added by
  `osin-horn-separator-is-opnorm-stable`.
