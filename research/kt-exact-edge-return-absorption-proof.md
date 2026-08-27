---
rg: 2
id: kt-exact-edge-return-absorption-proof
kind: route
title: Test the shortest fold theorem against every edge-commutant gauge
target: kt-exact-kun-thom-edge-return-is-algebraically-absorbed
requires:
  - kt-double-shortest-fold-repair-is-a-bare-wall
---

Let `pi:G->U(d)` be exact and let `U` be any unitary in
`C*(pi(Gamma))'`.  Define two exact representations

```text
rho_0=pi,                 rho_1=Ad(U) o pi.             (KEA4)
```

They agree pointwise on `Gamma`.  Part 1 of
`kt-double-shortest-fold-repair-is-a-bare-wall` therefore gives

```text
pi(h)=U pi(h) U^*.                                     (KEA5)
```

This holds for every unitary in `C*(pi(Gamma))'`.  Since the unitary group
linearly spans a finite-dimensional C-star algebra, `pi(h)` commutes with
the whole commutant.  The finite-dimensional bicommutant theorem yields

```text
pi(h) in C*(pi(Gamma))''=C*(pi(Gamma)).                (KEA6)
```

The trace-preserving conditional expectation onto that algebra fixes
`pi(h)`, and a unitary has normalized Hilbert--Schmidt norm one.  This is
`(KEA2)--(KEA3)`.

