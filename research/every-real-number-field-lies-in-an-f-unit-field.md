---
rg: 2
id: every-real-number-field-lies-in-an-f-unit-field
kind: claim
title: Every real algebraic number field is contained in Q(β) for some algebraic unit β > 1 with property (F); if so, every interval exchange group with algebraic parameters satisfies Boone--Higman
distinct_from:
  pisot-interval-exchange-groups-satisfy-boone-higman: that proves Boone--Higman for interval exchange groups over Q(β) with β a unit with (F); this asks whether those fields exhaust all real number fields, up to inclusion, which would remove the field restriction.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**OPEN.** A number-theoretic question with a Boone--Higman payoff.

**Question.** For every real number field `K`, is there an algebraic unit `β > 1` with property (F) — every
element of `Z[β] ∩ [0,1)` has a finite greedy β-expansion — such that `K ⊆ Q(β)`?

**Payoff.** If yes, `pisot-interval-exchange-groups-satisfy-boone-higman` applies to every finitely generated
interval exchange group whose lengths and translations are real algebraic numbers. That includes
- all Sturmian Juschenko--Monod groups with algebraic angles, and
- all derived full groups of minimal interval exchanges with algebraic lengths.

What would remain is transcendental parameters (`transcendental-slope-thompson-groups-satisfy-boone-higman`).

**What is known (from sources read, and elementary facts).**
- **Obstruction.** A unit with another positive real conjugate never has (F) (Akiyama, Proposition 1). So no
  real quadratic unit of norm +1 has (F), and fields such as `Q(√3)` are not of the form `Q(β)` with β quadratic.
  They could still lie inside a larger `Q(β)`.
  - `Q(√3)` is covered anyway, by `quadratic-interval-exchange-full-groups-satisfy-boone-higman` through the
    type (A) route.
- **Decidability.** (F) is decidable for a given Pisot β by a finite computation (Akiyama, Theorem 2). So
  candidate `β` for a given `K` can be tested.
- **Candidates.** Pisot units generating `K` exist in every real `K`: the unit lattice meets the open cone where
  only the real place is expanding. (F) is the real restriction. Powers `u^n` of a Pisot unit have a dominant
  trace coefficient, but sign conditions on the other coefficients are not controlled.
- **Families with (F).** Examples in every degree: the d-bonacci and plastic numbers.

No attempt at a proof has been made. The question is recorded as a precise reduction.
