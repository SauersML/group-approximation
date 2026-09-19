---
rg: 2
id: rational-ah-fourth-power-euler-tower-proof
kind: route
title: Kill all integral Euler relations by a mod-two fourth power and preserve top torsion through a simple rationally acyclic tower
target: rational-k-stable-simple-ah-torsion-counterexample
requires: []
artifacts:
  - research/artifacts/stw59-rational-k-stability-torsion-euler-tower-2026-09-05.md
---

1. The gauge fibration for a rank-r bundle E over a 2r-dimensional
   finite CW complex gives stabilization kernel H^(2r)(X;Z)/im Lambda_E.
   Derive Lambda_E integrally using the clutching class
   [E+1]+([H]-1)beta over S^2 times X and the splitting principle.
   Its formula uses integral Newton classes, retaining all torsion.
2. For E=F^(direct sum 4), reduction modulo two makes Lambda_E(beta)
   a fourth power for every virtual bundle beta. On a product with
   (RP^2)^4, fourth powers kill all positive degree from that factor,
   so a top-degree fourth power vanishes. Top integral cohomology is
   Z/2 and injects under reduction. Thus Lambda_E is identically zero.
3. Adding L^(direct sum r) over RP^(2r) multiplies the relative Euler
   obstruction by its nonzero top Chern class. Integral Thom-class
   multiplicativity applies without an orientable base. The resulting
   external product identifies the two top Z/2 groups.
4. Dense point evaluations in the actual unital twisted maps give
   simplicity. On unitary components, the evaluation block contracts
   to identity, so the component map is the identity-extension map
   just computed. Both kernel elements persist. Continuity of K1
   and unitary components proves that the entire limit kernel is Z/2.
5. Each base is rationally acyclic. The actual gauge evaluation map
   is a rational homotopy isomorphism by the fiberwise Gottlieb
   construction and mapping-space rationalization. The finite-rank
   unitary stable range makes each adjacent matrix map a rational
   isomorphism in any fixed positive degree at sufficiently late stages.
6. Doubling the bundle rank gives an integral stable range tending
   to infinity, so M_2(A) is K-stable. The exact one-half contraction
   of trace-space images gives a unique trace, faithful by simplicity,
   and hence stable finiteness.

The manuscript supplies all arguments, including the distinction
between the component kernel and the possibly nonzero stable K1 group.
No line-bundle-generation assumption is used for K^0.
