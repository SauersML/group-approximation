---
rg: 2
id: complete-commutation-overlay-proof
kind: route
title: Assign one repeated coordinate copy to every logical pair
target: quadratic-repetition-supports-complete-commutation-overlay
requires: []
---

There are `L-1` nontrivial partners for each base coordinate and at least `L`
copies, so the assignment `(i,j)` is injective within every equality cloud.
Each assigned copy is used in exactly one pair context.  A fixed-degree
equality graph adds only fixed additional degree, and the replicated LDPC
contexts also have bounded degree by construction.

At zero defect, connected equality graphs identify every copy in row `i`.
Substitution into `(QRC1)` gives `(QRC2)` for every unordered pair.  The
resulting base coordinate reflections are commuting involutions, hence have
one joint spectral PVM.  Every replicated local parity relation restricts
that PVM to the scalar LDPC kernel, proving the exact same-Hilbert statement.
