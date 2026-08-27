---
rg: 2
id: fanizza-final-bcs-has-fixed-nonlinear-menu
kind: claim
title: The Fanizza machine uses only three fixed nonlinear predicate shapes
distinct_from:
  fanizza-turing-bcs-signal-collapse: that imports the quantitative signal estimate and polynomial relator decompositions; this audits the truth tables that survive their final BCS flattening.
  relative-rank-one-fanizza-groupification: that must turn these predicates into group-word transport with HS payment; this only proves that the nonlinear packet menu is finite and machine-independent.
---

In the BCS family constructed in Section 5 of Fanizza--Kroell--Mehta--
Paddock--Rochette--Slofstra--Zhao, all machine-dependent nested-conjugacy
flattening constraints are linear.  Apart from the fixed linear BCS `B_H`,
the only nonlinear truth-table shapes in the final BCS are:

```text
C13/C14: (a AND q) = (b AND q)              (arity 3; 2 bad atoms),
C17:     d = (p AND q)                      (arity 3; 4 bad atoms),
C18:     A123(first triple) AND A456(last triple)
                                                    (arity 6; 20 bad atoms),
```

where, writing `-1` as bit one,

```text
A123={100,010,001,110,111},
A456={000,011,101,110}.                               (FNM1)
```

The second factor in `(FNM1)` is even parity.  (Display corrected
2026-08-22: the two predicates are the *equalities* named in the citation
route, and the bad-atom counts `2` and `4` are theirs; the inequality
`(a AND q) != (b AND q)` printed earlier has six bad atoms, and every
downstream use -- "choose the compared signs equal when `O_Q = -1`",
"`O_D` is the conjunction of `O_P, O_Q`" -- already followed the equalities.)  The other displayed contexts
`C1--C12,C15,C16` are equality, commutation-only, or linear constraints.
Theorem 5.5 flattens every nested conjugacy relation by adjoining copies of a
single 31-constraint linear BCS gadget; it preserves the original three
nonlinear predicate shapes and introduces no new nonlinear one.

The machine/input index changes word depth and the number of linear
flattening gadgets, but not this nonlinear menu.  In particular the current
groupification target is finite and runtime-independent, but it is not
correct to describe the Fanizza BCS as consisting only of binary
support-containment primitives.

For the **native prescribed-word groupification**, the last three C18
observables obey the Pauli relation only on preterminal addressed cells.  It
fails at the terminal cell, where the parity guard switches the recurrence
off.  Thus the fixed six-bit C18 predicate remains part of the native menu;
see `fanizza-pauli-guard-switches-off-at-the-terminal-cell`.
