---
rg: 2
id: rigidity-counterexample-from-leavitt-f2-linear-soficity
kind: route
title: If the binary Leavitt unit group is F_2-linear sofic, it is a finitely presented simple weakly sofic nonsofic group
target: fg-simple-weakly-sofic-nonsofic-group-exists
requires: [binary-leavitt-unit-group-is-f2-linear-sofic, leavitt-unit-group-is-simple-fa-nonsofic, linear-sofic-implies-weakly-sofic-over-every-field]
---

- **Hypotheses.** `R^x = L_(F_2)(1,2)^x` is finitely presented, simple and nonsofic
  (`leavitt-unit-group-is-simple-fa-nonsofic`).
- **Weak soficity.** If `R^x` is `F_2`-linear sofic, it is weakly sofic, because `GL_n(F_2)` is finite
  and the normalized rank length is bi-invariant (`linear-sofic-implies-weakly-sofic-over-every-field`).
- **Conclusion.** `R^x` is then a finitely generated simple weakly sofic nonsofic group.

The route fires only if `binary-leavitt-unit-group-is-f2-linear-sofic` is established. The same
argument applies over every field and to every finitely generated simple nonsofic group.
