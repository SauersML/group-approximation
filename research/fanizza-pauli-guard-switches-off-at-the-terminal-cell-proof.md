---
rg: 2
id: fanizza-pauli-guard-switches-off-at-the-terminal-cell-proof
kind: route
title: Evaluate the addressed Clifford commutator schedule in the exact HALT block model
target: fanizza-pauli-guard-switches-off-at-the-terminal-cell
requires:
  - msz-clifford-machine-skeleton-has-polynomial-fillings
  - msz-guarded-projection-recurrence-is-relation-r6
---

At halting time `n`, the exact completeness representation is block diagonal
over cells `0,...,n`.  The MSZ schedule gives commutator `J` before the
terminal cell and commutator `1` at the terminal cell.  Hence the global
commutator is `diag(J,...,J,1)`, not `J`.  The terminal difference is `1-J`
and has positive normalized Hilbert--Schmidt mass, explicitly `2/(n+1)` in
squared norm for the canonical trace.  Substitution into the guarded Fanizza
relation shows that this is exactly the block on which `1+J` switches the
recurrence off, proving `(FTG3)--(FTG6)`.
