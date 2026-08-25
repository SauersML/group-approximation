---
rg: 2
id: kt-kh-laurent-interface-local-instability-proof
kind: route
title: Localize the coefficient ring at the mixed root and apply Kazhdan local HS instability
target: kt-kh-laurent-interface-is-locally-hs-unstable
requires:
  - kt-elementary-kazhdan-packet-rounds-base-lamp
  - kt-ab-marked-return-is-the-first-mixed-cylinder
  - elementary-group-property-t-over-free-algebras
  - kun-thom-nonsofic-wreath
  - infinite-hyperlinear-kazhdan-group-is-not-hs-stable
---

The packet `K` generates every elementary matrix `e_ij(p)` with
`p in R_0`.  The mixed return is `h=e_12(s^(-1))`.  Constant elementary
Weyl words already in `Gamma` move this root to every off-diagonal slot, so
`<K,h>` contains `e_ij(s^(-1))` for all `i!=j`.

Use a spare index and the Steinberg relation

```text
[e_ik(a),e_kj(b)]=e_ij(ab).                                (KLI4)
```

Inductively, `(KLI4)` first gives every `e_ij(s^(-n))`, and then every
`e_ij(p s^(-n))` with `p in R_0`.  Same-slot additivity assembles arbitrary
coefficients of `R_0[s^(-1)]`.  Since

```text
x_i^(-1)=(product_(j!=i)x_j)s^(-1),
```

this localization is the full Laurent ring `R`.  Elementary generators
prove `(KLI2)`.

The ring `R` is a finite-type `F_2`-algebra, so the established rank-three
elementary theorem gives property `(T)` for `E` (and the same conclusion in
higher stable rank).  The Kun--Thom arithmetic actor is residually finite;
its subgroup `E` is therefore residually finite and hyperlinear.  It is
infinite because a root subgroup contains the infinite additive group of
`R`.

Apply `infinite-hyperlinear-kazhdan-group-is-not-hs-stable`, in its local
form, to the finite generating set `K union {h,h^(-1)}` from `(KLI2)`.  It
produces increasing-window asymptotic representations separated by a fixed
amount from every genuine same-dimensional representation on that generating
set.  This is exactly the negation of `(KLI3)`.

The theorem does not say that those bad actor microstates extend to the
complete Kun--Thom actor or to the Majorana presentation.  That extension
restriction is precisely the surviving route; dropping it would silently
assume a local stability statement which the cited theorem refutes.
