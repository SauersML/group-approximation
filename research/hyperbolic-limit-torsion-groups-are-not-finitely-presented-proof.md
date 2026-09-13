---
rg: 2
id: hyperbolic-limit-torsion-groups-are-not-finitely-presented-proof
kind: route
title: A finitely presented limit is a stage, and every stage has an element of infinite order
target: hyperbolic-limit-torsion-groups-are-not-finitely-presented
requires:
  - fp-direct-limit-of-quotients-equals-a-finite-stage
---

Suppose `G = F / U_i K_i` is finitely presented. By
`fp-direct-limit-of-quotients-equals-a-finite-stage`, `U_i K_i = K_i` for some
`i`, so `G = F / K_i`. By hypothesis `F / K_i` has an element of infinite order,
so `G` is not torsion. This contradicts the assumption.

For the hyperbolic case: an infinite word hyperbolic group contains an element
of infinite order (Gromov, *Hyperbolic groups*, 1987; standard, e.g. in the
Ghys–de la Harpe volume on Gromov's theory). Imported without a theorem number;
the general statement above does not use it.
