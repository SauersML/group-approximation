---
rg: 2
id: balanced-router-pauli-holonomy-interface
kind: claim
title: Expose the two Pauli quarter reflections through balanced derived-packet routers
requires:
  - hyperoctahedral-balanced-word-truth-table
  - full-conjugation-table-cancels-router-multiplicity
  - gauge-doubling-gives-selector-flip-symmetries
  - canonical-trace-tests-robustify-pauli-quarter-holonomy
distinct_from:
  derived-lifted-gauge-reset-spin-bridge: that renews a gauge selector at equal Schur spin scale; this asks only for two fixed Boolean Hecke phases and their common return comparison.
  mixed-relations-force-holonomy-or-transverse-recovery: that states the complete atlas dichotomy; this is the narrowed algebraic implementation of its holonomy branch.
---

OPEN.  The exact Pauli calculation has reduced the holonomy branch to a
finite truth-router interface.

Both quarter carriers are joint Boolean cuts of fixed involution selectors:

```text
F=(1-C_0)(1-C_1)/4,
G=(1-D_0)(1-D_1)/4.                                  (BRH1)
```

Their reflections `2F-1` and `2G-1` are the truth-table phase which is `+1`
only on the joint negative assignment and `-1` elsewhere (up to the chosen
global sign).  By `hyperoctahedral-balanced-word-truth-table`, each such phase
is a balanced word in one router and constants from a fixed derived
hyperoctahedral packet.  By
`full-conjugation-table-cancels-router-multiplicity`, the word is robust in an
arbitrary representation once the router's full conjugation table is named.

Construct one finite incidence satisfying all of:

1. the first router reads `(C_0,C_1)` and the second reads `(D_0,D_1)` on the
   actual atlas carrier;
2. all hyperoctahedral constants remain in one common finite type, so no
   second-layer multiplicity action changes the truth word;
3. gauge-doubling makes the selector translations honest symmetries of the
   exact marked representation;
4. the mixed rank-five return word requires the two derived truth phases to
   have trivial commutator (or identifies them after a named return); and
5. the exact nontrivial marked representation extends, using properly
   infinite multiplicity if needed.

Conditions (1)--(4), together with
`canonical-trace-tests-robustify-pauli-quarter-holonomy`, give an immediate
fixed normalized-HS contradiction: the return asks for zero energy while the
canonical trace window forces energy `1/2-o(1)`.  Condition (5) is the
completeness firewall; without it, imposing the return may simply collapse
the mark algebraically.

The truth-table and analytic-floor parts are proved.  The remaining work is
the finite equal-type incidence plus its exact properly infinite extension.
