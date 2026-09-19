---
rg: 2
id: right-regular-covariance-forces-one-common-router-proof
kind: route
title: Fourier support and finite conditional expectations leave one left translation coefficient
target: right-regular-covariance-forces-one-common-router
requires: []
---

The commutant of `rho(L) tensor I_H` consists exactly of operator-valued left
convolutions

```text
C=sum_(g in L) lambda(g) tensor V_g.                   (RRP1)
```

For a sign multiplier,

```text
(lambda(g) tensor V_g)(M_f tensor I)
 = M_(f(g^(-1) .)) (lambda(g) tensor V_g).
```

Consequently `(RRC3)` says that `V_g=0` unless

```text
f_j(gx)=epsilon_j f_j(x) for every j and x.            (RRP2)
```

By `(RRC2)` there is at most one such `g`, and it lies in `A`; the character
extensions identify it as the unique `a` satisfying `chi_j(a)=epsilon_j`.
Thus `(RRP1)` reduces to `lambda(a) tensor V`.  Since `C` is unitary, `V` is
unitary, proving `(RRC4)`.

For robustness, first average conjugation by the finite group `rho(L)`.
This is the trace-preserving conditional expectation onto its commutant, and
finite telescoping bounds the distance from `C` to its average by a fixed
multiple of the generator commutator defects.  On the commutant, the finitely
many maps

```text
T_j(X)=(M_(f_j) tensor I) X (M_(f_j) tensor I)
```

are commuting self-adjoint involutions in Hilbert--Schmidt space.  Their joint
spectral projections are finite averages.  Projecting to the prescribed
joint eigenspace and using `(RRC2)` leaves only the coefficient
`lambda(a) tensor V_a`; all other coefficients have squared norm bounded by a
fixed finite sum of the covariance defects.  Finally polar decomposition of
`V_a` changes it by at most another fixed multiple because the original `C`
is unitary.  Every averaging set is finite and fixed, so the resulting
constant is computable from `(L,f)` and is independent of `H`.

