---
rg: 2
id: symmetric-sign-packet-has-factorial-amitsur-density-loss
kind: claim
title: A regular symmetric-group sign packet loses the normalized Amitsur root by a factorial density factor
artifacts:
  - experiments/amitsur_sign_packet_density.py
distinct_from:
  raw-amitsur-permutation-sampling-has-factorial-gap-loss: that compares bounded local Gram windows with a regular simplex; this treats the exact global Fourier packaging by the full symmetric-group packet and finds the loss in its sign corner itself.
  bounded-local-unitary-sum-verifier-no-go: that permits arbitrary bounded-local auxiliary word checks and perturbs continuous scalar boundaries; this is an exact finite-packet trace and matrix-coefficient calculation on the Fock boundary.
  uniform-linear-pcpp-tensorizes-to-amitsur-hs: that conditionally retains the normalized root once a uniformly conditioned redundant proof exists; this shows that replacing such a proof by the bare regular sign idempotent does not retain it.
---

Let `m>=2`, put `N=m!`, and let `lambda` be the left regular
representation of `S_m`.  Its trivial and sign projections are

```text
e_+=(1/N) sum_(sigma in S_m) lambda(sigma),
e_-=(1/N) sum_(sigma in S_m) sgn(sigma)lambda(sigma).  (SPD1)
```

Both have rank one and normalized packet trace `1/N`.  Let `V_sigma` be
arbitrary operators on a Hilbert space and put

```text
D=sum_sigma |sigma><sigma| tensor V_sigma.             (SPD2)
```

Writing

```text
xi_+=(1/sqrt(N))sum_sigma |sigma>,
xi_-=(1/sqrt(N))sum_sigma sgn(sigma)|sigma>,           (SPD3)
```

the only sign-to-trivial coefficient of the controlled packet is

```text
(<xi_-| tensor 1) D (|xi_+> tensor 1)
  =(1/N)sum_sigma sgn(sigma)V_sigma.                   (SPD4)
```

The normalized Amitsur root is instead

```text
T=(1/sqrt(N))sum_sigma sgn(sigma)V_sigma.              (SPD5)
```

Thus the packet coefficient in `(SPD4)` is exactly `T/sqrt(N)`.  Recovering
`T` from this corner requires coefficient norm `sqrt(N)`, while using the
corner without renormalization loses a factor `1/N` in squared norm.  Its
ambient normalized packet Hilbert--Schmidt norm loses a second factor
`tau(e_-)=1/N`, hence

```text
||e_- D e_+||_(2,packet tensor H)^2
  =(1/N^2)||T||_(2,H)^2.                               (SPD6)
```

In the prefix-free Fock evaluation of the one-sided Amitsur oracle, the
`V_sigma` are isometries with pairwise orthogonal ranges.  Consequently
`T^*T=1`: the desired root has unit size, but its exact regular-packet block
has squared ambient size `1/N^2`.  Direct-sum amplification of the regular
packet changes neither `tau(e_-)=1/N` nor either ratio.

Therefore a bare symmetric-group lookup packet, even with its complete exact
multiplication table and exact sign projection, cannot be the constant-HS
localization layer for the dimension-reported Amitsur instruction.  A live
compiler must use a redundant proof with genuine gap amplification or a
delocalized terminal observable; global Fourier packaging alone retains the
same factorial normalization obstruction as raw sampling.

The audit script checks the sign-idempotent convolution identity exactly and
prints the scales in `(SPD4)--(SPD6)` for `2<=m<=7`.
