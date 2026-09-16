---
rg: 2
id: f2-support-three-one-sided-units-are-units
kind: claim
title: Over F_2, a group-ring element with support three and a one-sided inverse is a unit
distinct_from:
  dykema-heister-juschenko-bounded-rank-direct-finiteness: that settles the rank pairs (3,n) with n at most 11 by machine enumeration; this is the whole support-three row, with the partner support unbounded.
  z-fixed-support-three-elements-cannot-witness: that kills support-three elements fixing an order-three averaging idempotent, as in the Leavitt corner; this asks the same for every support-three element.
  f2-support-three-zero-divisors-need-support-at-least-22: that is about support-three zero divisors, the zero-divisor conjecture; this is about support-three one-sided units, direct finiteness.
  every-group-is-binary-surjunctive: that covers binary automata of every memory size; by binary-three-address-strict-automata-are-linear, this is exactly its case of at most three memory elements.
---

**OPEN.** For every group `G` and every `gamma in F_2[G]` with `|supp gamma| = 3`: if `beta gamma = 1`
or `gamma beta = 1` for some `beta in F_2[G]`, then `gamma` is a unit.

- **Normal form.** Up to multiplication by a group element on either side, `gamma = 1 + a + b` with
  `1, a, b` distinct.
- **Automaton form.** By `binary-three-address-strict-automata-are-linear` (artifact,
  Proposition 6.2), `1 + a + b` has a left inverse without being a unit iff
  `y -> y + R_a y + R_b y` is injective and not surjective on `{0,1}^G`.
- **Equivalence.** This claim holds iff every binary cellular automaton with at most three memory
  elements is surjunctive, over every group.

## Attempts

- **Small partner support (imported).** By `dykema-heister-juschenko-bounded-rank-direct-finiteness`,
  any one-sided inverse `beta` has `|supp beta| >= 12`. That result rests on a machine enumeration not
  replayed here.
- **Where the support sits.** Apply `subgroup-supported-one-sided-inverse-rigidity` with `H = <a, b>`.
  If `F_2[<a, b>]` is directly finite, `gamma` is a unit. This happens for instance when `<a, b>` is
  sofic, or linear sofic over `F_2` (`linear-sofic-group-algebra-is-stably-finite`). So a
  counterexample needs a two-generated group `<a, b>` whose group algebra over `F_2` is not directly
  finite.
- **Special elements.** `z-fixed-support-three-elements-cannot-witness` excludes elements fixing an
  order-three averaging idempotent.
- **Backgrounds (2026-09-16, swarm-every-group-is-binary-surjunct).** The configuration tests that
  kill every non-affine three-address rule do not touch this linear case.
  - Constant backgrounds: `L'(1) = 1`.
  - Coset backgrounds: `L'(1_H) = 1_H` for every subgroup `H` containing `a, b`.
  - Single flips: `L'(delta_k)` has weight three.
  - Where it dies: a collision for the linear map is a nonzero kernel element `y`, possibly of
    infinite support. That is a global dual-rank question, not a local blind-flip question.
