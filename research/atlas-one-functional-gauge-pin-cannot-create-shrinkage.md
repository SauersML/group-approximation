---
rg: 2
id: atlas-one-functional-gauge-pin-cannot-create-shrinkage
kind: claim
title: One linear Atlas gauge pin cannot create a legitimate shrunk operator space
distinct_from:
  atlas-phase-jacobian-has-invertible-gauge-kernel: that treats the unpinned Jacobian and its invertible gauge tangent; this proves that the honest one-functional quotient is real-linear and that its complexification restores an invertible direction.
  fixed-rank-index-authenticator-has-gap-or-functoriality: that gives a hard-rank and spectral-gap dichotomy; this gives the explicit Lipschitz/instability dichotomy for scalar phase normalization and identifies the tangent-space obstruction.
  atlas-spectral-shrunk-intertwiner-certificate: that allows any microstate-dependent complex low-energy space; this rules out obtaining it by one scalar linear phase condition on the raw phase-cycle Jacobian.
---

**ESTABLISHED FIREWALL.**  Fix a contraction `A in M_d(C)` and the linear
functional

```text
ell(U)=tr_d(A^*U).                                    (OFG1)
```

On `ell(U)!=0`, the usual scalar gauge pin is

```text
G(U)=overline(ell(U))/|ell(U)| * U,                   (OFG2)
```

so that `ell(G(U))>0`.  This operation cannot supply the missing Atlas
shrunk-space invariant.

First, on the region `|ell(U)|>=c>0`, it is uniformly Lipschitz:

```text
||G(U)-G(V)||_2 <= (1+2/c)||U-V||_2.                  (OFG3)
```

Every phase holonomy is unchanged by `(OFG2)`, and every additive phase row
is multiplied by one scalar unitary.  Hence all nonlinear defects, singular
values, and normalized-HS energies in the five-row problem are exactly
unchanged.  A stable pin is therefore only a choice of coordinates on the
same scalar orbit; it creates no gap.

Second, the honest infinitesimal slice is not a complex matrix space.  After
pinning so that `ell(U)>0`, its ambient real tangent equation is

```text
S_U={T in M_d(C): Im ell(T)=0}.                        (OFG4)
```

It removes the scalar tangent `iU`, but contains `U`.  Its complex linear
span therefore contains the invertible matrix `U`, so for every
`X<=C^d`,

```text
dim span_C(S_U)(X) >= dim UX=dim X.                   (OFG5)
```

Thus the complexification required by operator scaling has no shrunk
subspace.  Replacing `(OFG4)` by the complex hyperplane `ker ell` is not a
gauge quotient: it imposes two real equations and deletes the additional
radial direction detected by `Re ell`, rather than only the one-dimensional
circle orbit.  Any shrinkage created by that stronger cut is not certified
by the scalar symmetry.

Finally, without a uniform lower bound on `|ell(U)|`, phase pinning has no HS
modulus.  Already for `A=I_2` and

```text
U_t=diag(exp(it),-exp(-it)),
```

one has `||U_t-U_(-t)||_2->0` but, for `t>0`, the two pinned matrices tend to
opposites and

```text
||G(U_t)-G(U_(-t))||_2 ->2.                            (OFG6)
```

Consequently one linear functional offers only this dichotomy:

```text
uniformly nonzero pin  => stable but phase-energy neutral;
possibly zero pin      => no dimension-independent HS control. (OFG7)
```

A viable gauge-pinned singular-space route needs additional algebraic data
which both pays for a nonvanishing pin and produces a genuinely complex
relative operator space after quotienting; one raw linear functional does
neither.
