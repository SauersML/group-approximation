---
rg: 2
id: bounded-bs14-full-commutant-coboundary-proof
kind: route
title: Decompose the base commutant by spectral orbit and Fourier-invert its finite adjoint action
target: bounded-bs14-full-commutant-coboundary-inverse
requires:
  - bs14-unitary-representations-are-periodic-cycle-packets
---

Group the scalar packet normal form by fourth-power spectral orbit.  For an
orbit `O` of length `m<=K`, the corresponding part `Z_O` of `{S}'` contains
all matrices between scalar packets carrying `O`, at equal orbit coordinate.
If their return phases are `w_a`, then on the matrix unit
`E_(j;a,b)` the `m`th power of `psi=Ad(R)` acts by the scalar

```text
w_a conjugate(w_b).
```

This scalar has order dividing `M`, so

```text
psi^(mM)=1 on Z_O.                                    (BFP1)
```

Consequently every nontrivial eigenvalue of `psi|_(Z_O)` is a root of unity
of order at most `mM<=KM`.  Its distance from one is therefore at least

```text
2 sin(pi/(KM)).                                       (BFP2)
```

The orbit blocks are Hilbert--Schmidt orthogonal and exhaust `Z`.  Spectral
functional calculus for the unitary `psi` now inverts `1-psi` on the
orthogonal complement of its fixed algebra, giving the first inequality in
`(BFC2)`.  Since `pi/(KM)<=pi/2` and `sin t>=2t/pi` on `[0,pi/2]`, the second
inequality follows.
