---
rg: 2
id: classical-pcp-gap-is-not-tracial-pvm-gap
kind: claim
title: Classical PCP unsat does not lower to forbidden mass for contextual tracial PVMs
distinct_from:
  trace-functorial-bcs-signal-groupification-impossible: that rules out a trace-functorial decoder from a marked group word; this directly refutes the use of a classical global-assignment soundness proof on contextwise operator assignments.
  multiplicity-surplus-is-blind-to-the-non-ce-input: that shows scalar forbidden mass alone cannot distinguish classical from non-CE unsatisfiability; this shows classical UNSAT and tracial forbidden mass can point in opposite directions on the same BCS.
---

There is a finite BCS `B` for which

```text
UNSAT_classical(B)>0                                          (CPQ1)
```

but which has a tracial operator assignment with every forbidden joint
spectral projection equal to zero. Consequently no universal inequality of
the form

```text
tracial forbidden mass >= c UNSAT_classical(B),       c>0,    (CPQ2)
```

holds for contextwise commuting PVM assignments.

In particular, Dinur's popular-assignment and random-walk hit argument cannot
be applied verbatim after replacing classical vertex labels by independently
commuting context PVMs. A quantum gap-amplification route must add an
answer-reduction/synchronization theorem or use a finite-dimensional
multiplicity feature which has no tracial analogue.

