---
rg: 2
id: non-weakly-sofic-group-exists
kind: claim
title: Some group is not weakly sofic
distinct_from:
  non-weakly-sofic-finitely-presented-reduction: that transfers a hypothetical non-weakly-sofic group to a finitely presented one; this is the existence statement itself.
  weakly-sofic-not-sofic: that separates weak soficity from soficity through a weakly sofic nonsofic group; this asks for a group outside the weakly sofic class.
  binary-leavitt-unit-group-is-weakly-sofic: that asks whether one explicit simple nonsofic group is weakly sofic; a negative answer there would establish this claim.
root: true
---

**Root (2026-09-13, ex-steward).** Glebsky--Rivera, J. Algebra 320 (2008), Conjecture 4.5, as stated below.

**OPEN.** There is a countable group that is not weakly sofic in the sense of Glebsky--Rivera
(Definition 4.1 of J. Algebra 320 (2008)). This is their Conjecture 4.5, equivalent by their
Corollary 4.6 to the bounded-width certificate recorded in
`research/artifacts/non-weakly-sofic-word-certificate.md`.

Reinstated as an open node by lane ex-weak-soficity (2026-09-12), whose brief is this problem.
The earlier demotion to an artifact (`research/artifacts/non-weakly-sofic-group.md`) was a
scoping decision of another program, not a change in the mathematics.

**Fixed tests.** By `universal-local-approximation-fixed-two-generator-test-group` and
`fixed-finite-relator-quotient-tests-local-permanence`, this claim holds iff one fixed
two-generator finitely presented group is not weakly sofic, iff weak soficity is not closed under
quotients.

## Attempts

- **Certificates.**
  - *Howie's tuple.* The one explicit candidate on record fails at `A_5`
    (`howie-pro-p-tuple-fails-the-profinite-certificate-at-a5`).
  - *Nilpotent width.* Bounded relator width over nilpotent groups is automatic for perfect
    presentations (`perfect-group-relator-width-over-nilpotent-groups`), so it carries no information.
- **Through simple groups.**
  - *The reduction.* Route `non-weakly-sofic-group-from-simple-weak-sofic-rigidity`: if finitely
    generated simple weakly sofic groups are sofic, this claim follows.
  - *Evidence.* For finitely presented simple nonsofic groups, the width certificate already holds
    over every symmetric, alternating, sporadic, bounded-rank Lie type and nilpotent group
    (`simple-group-relator-width-in-finite-simple-targets`,
    `perfect-group-relator-width-over-nilpotent-groups`).
  - *Exact target (2026-09-13, lane `ex2-weak-sofic-bounded-factors`, unreviewed).* An infinite finitely
    presented simple group is not weakly sofic iff it is not linear sofic over finite fields
    (`fp-simple-weak-soficity-is-finite-field-linear-soficity`). Two routes lead there: Nikolov--Schneider--Thom
    Theorem 4 with the PSL dichotomy, and a width-form route through `relator-width-bounded-by-almost-simple-quotients`.
    So this claim follows from one finitely presented simple group, such as `R^x` or Thompson's `V`, that embeds in no
    rank-metric ultraproduct of groups `GL_n(F_q)`. Conversely, for simple candidates nothing weaker can work: every
    certificate over finite groups is a non-linear-soficity certificate over finite fields.
- **Concrete candidate.** The binary Leavitt unit group (`binary-leavitt-unit-group-is-weakly-sofic`),
  finitely presented, simple, Kazhdan and nonsofic.
