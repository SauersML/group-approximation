---
rg: 2
id: vanishing-weight-full-actor-leakage-proof
kind: route
title: Hide the small-rotation diagonal calibration in a negligible actor block
target: vanishing-weight-block-carries-full-actor-edge-leakage
requires:
  - kt-exact-kun-thom-edge-return-is-algebraically-absorbed
---

Write `m_r=2^r`.  On `C^(m_r)` let `D_r` be the Fourier diagonal algebra of
`C_2^r`, and let `U_r` be the direct sum of `m_r/2` real rotations through

```text
theta_r=m_r^(-1/4).
```

The calculation in
`small-rotation-canonical-edge-leakage-proof` gives

```text
||(1-E_(D_r))Ad(U_r)E_(D_r)||_HS^2
  =(m_r/2)sin^2(2theta_r) ~ 2sqrt(m_r).                 (VBP1)
```

Choose exact finite-image representations

```text
rho_r:G->U(N_r)
```

whose characters converge to the canonical character; residual finiteness
supplies finite quotient regular representations, and arbitrary common
amplification lets us arrange

```text
delta_r=m_r/(N_r+m_r)->0.                              (VBP2)
```

We now define an arbitrary unitary table `psi_r:G->U(m_r)`.  Put
`psi_r(1)=1`, `psi_r(t)=U_r`, choose `r` elements of the infinite group
`Gamma` whose images are the coordinate sign generators of `D_r`, and send
all remaining elements of `Gamma` into `D_r`.  This can be done with

```text
C*(psi_r(Gamma))=D_r.                                  (VBP3)
```

There is one harmless technical point needed to split the two physical
blocks inside the generated edge algebra.  Choose `k_r in Gamma` and a scalar
`zeta_r` outside the finite spectrum of `rho_r(k_r)`, and prescribe
`psi_r(k_r)=zeta_r 1`.  Polynomial functional calculus applied to

```text
rho_r(k_r) direct_sum zeta_r 1
```

then puts the calibration-block central projection in the generated algebra.
Together with `(VBP3)` this gives

```text
C*((rho_r direct_sum psi_r)(Gamma))
  =C*(rho_r(Gamma)) direct_sum D_r.                    (VBP4)
```

Define

```text
phi_r(g)=rho_r(g) direct_sum psi_r(g).                  (VBP5)
```

The second block need not respect any relation.  Nevertheless, for fixed
`g,h in G`, exactness of `rho_r` and `(VBP2)` give

```text
||phi_r(gh)-phi_r(g)phi_r(h)||_2^2 <=4delta_r->0.       (VBP6)
```

Likewise, for fixed `g!=1`,

```text
|tr(phi_r(g))|
 <=(1-delta_r)|tr(rho_r(g))|+delta_r->0.               (VBP7)
```

Thus `(VBP5)` is a canonical approximate representation of the actual full
actor, and all fixed words involving its actual strict compressor `t` are
automatically covered by `(VBP6)`.

Put `B_r=C*(phi_r(Gamma))`.  Since
`t Gamma t^(-1)<Gamma`, conjugation by `rho_r(t)` maps
`C*(rho_r(Gamma))` into itself.  A unital finite-dimensional algebra and its
unitary conjugate have the same dimension, so this inclusion is equality and
the dominant block contributes zero edge leakage.  By `(VBP4)`, the
calibration block contributes exactly `(VBP1)`.  Scaling the physical trace
on one direct summand rescales both the domain basis and its image and hence
does not change the unnormalized Hilbert-space Hilbert--Schmidt norm of the
restricted superoperator.  Therefore

```text
||(1-E_(B_r))Ad(phi_r(t))E_(B_r)||_HS^2
  =(m_r/2)sin^2(2theta_r)->infinity,                    (VBP8)
```

which proves `(VBL1)`.

Finally fix `gamma in Gamma\t Gamma t^(-1)` and
`h=t^(-1)gamma t`.  The exact finite-dimensional absorption theorem gives

```text
rho_r(h) in C*(rho_r(Gamma)).                           (VBP9)
```

The squared normalized `L2` mass of that dominant block is `1-delta_r`.
Hence

```text
||E_(B_r)(phi_r(h))||_2^2>=1-delta_r->1,               (VBP10)
```

proving `(VBL2)` and locating precisely why the construction does not meet
the reduced relative expectation.
