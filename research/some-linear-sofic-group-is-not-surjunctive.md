---
rg: 2
id: some-linear-sofic-group-is-not-surjunctive
kind: claim
title: For some prime p, some group that is linear sofic over F_p carries an injective non-surjective cellular automaton
refuted_by:
  - linear-sofic-groups-are-surjunctive
distinct_from:
  linear-sofic-nonsofic-group: that asks for a complex linear sofic group that is not sofic; a witness here is linear sofic over a prime field and, by Gromov and Weiss, not sofic, so it would separate the classes over a finite field and refute Gottschalk's conjecture at once.
  leavitt-unit-group-nonsurjunctive: that names one host; this asks for any host in the linear sofic class, which is the class the rank gate asks about for that host.
artifacts:
  - research/artifacts/linear-sofic-rung-rank-implication-2026-09-12.md
---

**OPEN.** For some prime `p` there is an `F_p`-linear sofic group that is not surjunctive.

**Matrix form.** By `linear-sofic-surjunctivity-is-a-rank-implication-per-datum`, this holds iff some strict
datum `D` and prime `p` admit, for every reverse word `w`, some `eps_w > 0` and tuples of invertible matrices over
`F_p` whose forward relators have normalized rank tending to `0` while `w` keeps normalized rank at least `eps_w`.

**What a witness group `K` would be.**
- **Nonsofic.** By `sofic-groups-are-surjunctive`.
- **Stably finite over `F_p`.** By `linear-sofic-group-algebra-is-stably-finite`. So its strict automata are
  nonlinear, and over `p`-power alphabets no strict pair is formalizable, even after identity tracks
  (`formalizable-strict-pairs-certify-non-linear-soficity`).
- **Weakly sofic.** So it refutes `metric-ultraproducts-of-finite-groups-are-surjunctive`, and the goal.

## Attempts

- **Monomial tuples never witness.** On monomial tuples the implication holds for every strict datum
  (`gromov-weiss-is-the-monomial-case-of-the-rank-implication`). The same holds for tuples within small rank of
  monomial ones, generator by generator, so witnessing tuples stay far from monomial.
- **The rules cannot be run on witnessing tuples.** The coordinatewise product through which nonlinear rules are
  evaluated is not stable under small rank errors (`site-pullbacks-are-discontinuous-in-the-rank-metric`). So no
  counting of configurations applies, and a witness is invisible to Gromov–Weiss counting by construction.
- **Test host.** If `binary-leavitt-unit-group-is-f2-linear-sofic` and `leavitt-unit-group-nonsurjunctive` both hold,
  `R^x` witnesses at `p = 2`. Neither is decided.
- **Where it stops.** No strict datum has been tested against nonmonomial tuples. The natural far-from-monomial
  family is unipotent tuples, which carry relations that no Hamming model carries
  (`unipotent-frame-relations-cannot-assemble-corner-cuntz-family`).
