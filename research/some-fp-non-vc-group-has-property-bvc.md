---
rg: 2
id: some-fp-non-vc-group-has-property-bvc
kind: claim
title: Some finitely presented group with property BVC is not virtually cyclic
---

The negation of `finitely-presented-bvc-groups-are-virtually-cyclic`: a finitely presented
group `G`, not virtually cyclic, with finitely many virtually cyclic subgroups into which
every virtually cyclic subgroup is conjugate.

## Attempts

- Constraints any example must meet (von Puttkamer–Wu 1607.03790; Barnea–Camina–Ershov–Lewis
  2210.15746): not residually finite; not finitely generated linear; no non-ascending HNN
  splitting (Lemma 2.4); abelianization of rank at most one (Corollary 1.15); bounded orders
  of finite subgroups (Lemma 1.7); not virtually solvable; not one-relator, acylindrically
  hyperbolic, 3-manifold, or CAT(0) with a rank-one isometry or `Z^2`.
- Candidate shape: an infinite finitely presented torsion-free group with finitely many
  conjugacy classes would do (Corollary 1.5 of 1607.03790). Osin's examples are finitely
  generated but not finitely presented. The counterexample side belongs to lane z1-07-vc-counter.
- Reductions (lane z1-07-vc-counter):
  - `bvc-counterexample-from-fp-torsion-free-few-class-group`, from
    `some-infinite-fp-torsion-free-group-has-finitely-many-classes`. Such a group has property
    FA, and every infinite-order element is distorted.
  - `bvc-counterexample-from-fp-torsion-group-with-bvc`, from
    `some-fp-infinite-torsion-group-has-bvc`, which is Problem 1.11 plus BVC.
- More obstructions (lane z1-07-vc-counter):
  - An amalgam `A *_C B` with BVC acts 2-transitively on both coset spaces
    (`bvc-amalgams-have-two-transitive-vertex-actions`); Higman's group fails this.
  - A group of homeomorphisms of the line without global fixed point, containing a
    compactly supported element with finitely many support components, lacks BVC
    (`line-groups-with-bounded-support-lack-bvc`); this covers `[F, F]` and simple
    examples.
  - Candidate table with killing hypotheses:
    `research/artifacts/zp-vc-counterexample-candidates-2026-09-13.md`.
