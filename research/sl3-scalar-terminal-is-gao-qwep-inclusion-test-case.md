---
rg: 2
id: sl3-scalar-terminal-is-gao-qwep-inclusion-test-case
kind: claim
title: The scalar SL3 terminal is a concrete test case for Gao's QWEP-inclusion problem
distinct_from:
  sl3-re-over-lattice-iff-re-over-scalars: that removes the lattice coefficient; this locates the resulting scalar problem inside Gao's general open QWEP-inclusion question.
  sl3-arithmetic-inclusion-is-not-re-over-scalars: that asserts the negative answer for this inclusion; this is the unconditional implication relating it to the general question.
---

Put `N=L(SL_3(Z))` and `M=L(SL_3(Z[1/2]))`.  Both `N` and `M` are QWEP,
yet whether `N subset M` is `RE/C_scalar` is open.  Consequently:

1. a positive theorem that every inclusion into a finite QWEP algebra is
   scalar relatively embeddable would refute
   `sl3-arithmetic-inclusion-is-not-re-over-scalars`;
2. establishing that SL3 scalar terminal would give a concrete negative
   answer to Gao's Problem 6.1.

Thus QWEP or Connes embeddability of the ambient arithmetic factor cannot
itself be used as evidence for the desired negative statement.  The
obstruction must involve the position of `N` inside `M` and the commuting
square, not embeddability of either factor separately.

