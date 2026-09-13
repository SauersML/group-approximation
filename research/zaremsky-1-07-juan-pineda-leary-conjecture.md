---
rg: 2
id: zaremsky-1-07-juan-pineda-leary-conjecture
kind: claim
title: "Zaremsky Problem 1.7 resolved: decide the Juan-Pineda–Leary and von Puttkamer–Wu conjectures on virtually cyclic subgroups"
root: true
distinct_from:
  groups-with-finite-evc-model-are-virtually-cyclic: that claim is the affirmative answer to the first conjecture alone; this is the two-part question, established only by a consistent pair of answers
  finitely-presented-bvc-groups-are-virtually-cyclic: that claim is the affirmative answer to the second conjecture alone; this is the two-part question
artifacts:
  - research/artifacts/zp-jpl-bvc-known-classes-2026-09-13.md
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 7, verbatim:

"Conjecture of Juan-Pineda–Leary: If a group admits a finite classifying space for
the family of virtually cyclic subgroups, then the group is virtually cyclic. Related
Conjecture of von Puttkamer–Wu: If a finitely presented group has finitely many
virtually cyclic subgroups into which all virtually cyclic subgroups are conjugate,
then the group is virtually cyclic."

**Reading.** For a group `G`, `E_VC G` is a `G`-CW complex whose fixed set `X^H` is
contractible when `H` is virtually cyclic and empty otherwise. A model is *finite* when
it has finitely many `G`-orbits of cells.

- Part (A) is Juan-Pineda–Leary, *On classifying spaces for the family of virtually
  cyclic subgroups*, Contemp. Math. 407 (2006), Conjecture 1: a group with a finite
  model for `E_VC G` is virtually cyclic.
- Part (B) uses property (BVC): there are finitely many virtually cyclic subgroups
  `V_1, ..., V_n` (a *witness*) such that every virtually cyclic subgroup of `G` is
  conjugate into some `V_i`. The conjecture is von Puttkamer–Wu, arXiv:1607.03790
  (Groups Geom. Dyn. 13 (2019) 707–729), Conjecture B: a finitely presented group with
  BVC is virtually cyclic. The finite presentation is needed: Osin's finitely generated
  torsion-free groups with exactly two conjugacy classes have BVC (loc. cit., Remark (a)).

**Relation between the parts.** A finite model for `E_VC G` makes `G` finitely presented
with BVC (`finite-evc-model-implies-fp-and-bvc`). So (B) implies (A)
(`jpl-conjecture-from-conjecture-b`), and a counterexample to (A) is a counterexample to (B)
(`bvc-counterexample-from-jpl-counterexample`).

This claim is the question. It is established only through an answer route that settles
both parts:

- **Yes and yes**: `zaremsky-1-07-by-yes` requires
  `groups-with-finite-evc-model-are-virtually-cyclic` and
  `finitely-presented-bvc-groups-are-virtually-cyclic`.
- **No and no**: `zaremsky-1-07-by-no` requires `some-non-vc-group-has-a-finite-evc-model`
  and `some-fp-non-vc-group-has-property-bvc`.
- **Yes for (A), no for (B)**: `zaremsky-1-07-by-split` requires
  `groups-with-finite-evc-model-are-virtually-cyclic` and
  `some-fp-non-vc-group-has-property-bvc`.

"No for (A), yes for (B)" cannot happen, by the relation above. Never write a
`requires: []` route into this claim.

**Known cases** (statements checked against the papers; details, page numbers and scope
in the artifact):

- (A) holds for hyperbolic groups (Juan-Pineda–Leary 2006, Corollary 12) and for
  elementary amenable groups (Kochloukova–Martínez-Pérez–Nucinkis, Bull. LMS 43 (2011),
  arXiv:0903.4079), and for Artin groups (von Puttkamer–Wu, arXiv:1807.10095).
- BVC implies virtually cyclic for virtually solvable groups (Groves–Wilson, Bull. LMS 45
  (2013); von Puttkamer–Wu 1607.03790, Proposition 1.12); for finitely generated groups
  that are HNN extensions of finite-rank free groups, one-relator groups, acylindrically
  hyperbolic groups, 3-manifold groups, or CAT(0) groups with a rank-one isometry or `Z^2`
  (1607.03790, main theorem); for finitely generated linear groups (von Puttkamer–Wu,
  arXiv:1704.05304, Theorem I); and for residually finite groups (Barnea–Camina–Ershov–Lewis,
  arXiv:2210.15746, Theorem 1.1 with Lemma 8.2, the argument of Corollary 8.4).
- So any counterexample to (B) is not residually finite, not linear, has abelianization of
  rank at most one, and splits as no non-ascending HNN extension.

## Attempts

- 2026-09-13 (lane z1-07-vc-proof): status sweep. The arXiv metadata search for
  "Juan-Pineda Leary" returns only the three von Puttkamer–Wu papers. The 2025
  Barnea–Camina–Ershov–Lewis paper settles residually finite groups. No resolution of
  either conjecture was found (bounded search: arXiv metadata, general web search; no
  MathSciNet or zbMATH).
- Partial results (lane z1-07-vc-proof, 2026-09-13; unreviewed, review requested):
  - `elementary-amenable-finite-hirsch-length-bvc-groups-are-vc`: extends Proposition 1.12
    from virtually solvable groups to elementary amenable groups of finite Hirsch length. The
    elementary amenable remainder is `bvc-elementary-amenable-groups-have-finite-hirsch-length`
    (route `ea-bvc-vc-via-finite-hirsch-length` into `elementary-amenable-bvc-groups-are-virtually-cyclic`).
  - `fp-bvc-group-mapping-onto-z-is-ascending-hnn-extension`: finitely presented BVC groups with
    positive virtual first Betti number are virtually cyclic or have a finite-index ascending
    HNN extension of an infinite finitely generated base.
  - `bvc-bounds-conjugacy-classes-in-fibers-of-maps-to-z`: `R(alpha^m) <= m·C`.
  - `osin-group-times-z-has-bvc`: finite presentation is needed even with infinite
    abelianization.
- Where it stops: (1) elementary amenable groups of infinite Hirsch length, where Lemma 1.13(c)
  bounds the number but not the rank of non-torsion normal factors; (2) ascending HNN
  extensions of infinite finitely generated groups, where finite presentation must be used
  beyond conjugacy counting; (3) finitely presented BVC groups all of whose finite-index
  subgroups have finite abelianization, the few-conjugacy-class monster shape. Peer lane
  z1-07-vc-counter works the counterexample side.
