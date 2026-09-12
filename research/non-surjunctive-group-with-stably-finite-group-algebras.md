---
rg: 2
id: non-surjunctive-group-with-stably-finite-group-algebras
kind: claim
title: Some group whose prime-field group algebras are all stably finite is not surjunctive
distinct_from:
  leavitt-unit-group-nonsurjunctive: that asks for a counterexample on one specific host by any mechanism, including the Kaplansky route; this asks for a counterexample on a host where the Kaplansky route is closed, so the automaton must be nonlinear in an essential way.
  gottschalk-surjunctivity-conjecture: that is the universal positive statement; this is a sharper negation that excludes counterexamples coming from one-sided inverses in group algebras.
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

**OPEN.** There is a group `G` with `F_p[G]` stably finite for every prime `p`, and a finite alphabet,
carrying an injective cellular automaton that is not surjective.

**Why it is a separate target.** By `formal-polynomial-strict-pairs-need-unstable-linearization`, on
such a host every strict pair over an alphabet `F_q^n` must use the collapse `x^q = x` essentially in
its left-inverse identity. Its linearization at a constant configuration satisfies
`J_sigma J_tau = 1 + D(c)` for a nonzero collapse defect `D(c)`. No one-sided inverse in a group
algebra can witness it.

## Attempts

- **Formal designs.** Dead on such hosts: shears, triangular circuits, Nagata-type designs, and
  specializations of polynomial identities over infinite fields or `F_p[t]` are bijective (Theorem 1
  and Corollaries 2–3 of the artifact).
- **Where the collapse sits.** For `q = 2` with multilinear rules, `sigma o tau - id` has the form
  `sum_h (X_h^2 - X_h) P_h`, and the squares arise only at forward coincidences
  `g s m = g s' m'`. So the collapse terms live on the forward table, and the canonical table-group
  filters apply to them. No invariant is known that forces the collapse polynomial to vanish, and no
  collapse-essential strict pair is known on any group. This is where the attempt currently stops.
