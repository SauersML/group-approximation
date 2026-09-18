---
rg: 2
id: every-real-number-field-lies-in-an-f-unit-field
kind: claim
title: Every real algebraic number field is contained in Q(β) for some algebraic unit β > 1 with property (F); if so, every interval exchange group with algebraic parameters satisfies Boone--Higman
refuted_by:
  - f-unit-fields-are-characterized-by-isolated-sign-units
distinct_from:
  pisot-interval-exchange-groups-satisfy-boone-higman: that proves Boone--Higman for interval exchange groups over Q(β) with β a unit with (F); this asks whether those fields exhaust all real number fields, up to inclusion, which would remove the field restriction.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**REFUTED** by `f-unit-fields-are-characterized-by-isolated-sign-units` (09-18). `Q(√3)` lies in no (F)-unit field: every
unit of `Q(√3)` has norm +1, so none has an isolated sign, which the refuting node shows is necessary. The
surviving question is which fields with complex places satisfy the argument condition of item 3 there.

Original question (kept for the record):

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
  - `Q(√3)` is covered anyway, by `algebraic-interval-exchange-groups-satisfy-boone-higman` through negative-base
    codings. That node covers every real number field, so the Boone--Higman purpose of this question is met
    without (F). (An earlier line here credited the type (A) route; that route was withdrawn for norm +1 fields.)
- **Decidability.** (F) is decidable for a given Pisot β by a finite computation (Akiyama, Theorem 2). So
  candidate `β` for a given `K` can be tested.
- **Candidates.** Pisot units generating `K` exist in every real `K`: the unit lattice meets the open cone where
  only the real place is expanding. (F) is the real restriction. Powers `u^n` of a Pisot unit have a dominant
  trace coefficient, but sign conditions on the other coefficients are not controlled.
- **Families with (F).** Examples in every degree: the d-bonacci and plastic numbers.

No attempt at a proof has been made. The question is recorded as a precise reduction.
