---
rg: 2
id: classical-pcp-gap-is-not-tracial-pvm-gap-proof
kind: route
title: Use a tracial but non-Connes-embeddable BCS
target: classical-pcp-gap-is-not-tracial-pvm-gap
requires:
  - mipstar-bcs-tracial-nonru-exists
---

Let `B` be the finite BCS supplied by the prerequisite: its BCS algebra has a
tracial state but no Connes-embeddable tracial state. A classical satisfying
assignment would define a one-dimensional representation and therefore a
Connes-embeddable tracial state. Hence no classical satisfying assignment
exists. Since the constraint set is finite, its classical UNSAT is positive,
proving `(CPQ1)`.

On the other hand, the given tracial state evaluates the BCS generators as
contextwise commuting involutions satisfying every constraint. Every
forbidden joint spectral projection therefore vanishes in the tracial GNS
algebra. Its total forbidden mass is zero, contradicting `(CPQ2)` for every
`c>0`.

