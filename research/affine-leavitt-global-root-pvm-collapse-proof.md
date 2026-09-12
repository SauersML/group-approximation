---
rg: 2
id: affine-leavitt-global-root-pvm-collapse-proof
kind: route
title: Sum infinite-orbit PVM Poincare inequalities and bound the active root
target: affine-leavitt-global-root-pvm-collapses-active-mark
requires:
  - affine-leavitt-active-root-character-orbits-are-aperiodic
  - infinite-schreier-pvm-transport-kills-finite-mark
---

Only finitely many character projections are nonzero.  Split their support
into `H`-orbits and apply the infinite Schreier PVM inequality on each
nontrivial orbit.  The gap `gamma` is uniform by property `(T)`, so summing
gives `(AGC1)`.  The trivial character contributes zero to
`rho(m_0)-I`; on every other character the squared scalar distance to one is
at most four.  Hence

```text
||rho(m_0)-I||_2^2
 <= 4 sum_(chi!=1) tr(P_chi)
 <= 2 E_act/gamma.
```

Finite presentation and nontriviality of the active root are the same
rank-stable Steinberg facts used by
`affine-leavitt-steinberg-mark-is-fd-invisible`.

