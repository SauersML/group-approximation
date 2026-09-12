---
rg: 2
id: hilbert-hotel-model-full-mf-radical-proof
kind: route
title: Compress a Kazhdan corner and spread one full root defect
target: hilbert-hotel-model-full-mf-radical
requires:
  - kazhdan-asymptotic-commutant-transport
  - norm-matrix-corona-has-no-proper-isometries
  - elementary-group-property-t-over-free-algebras
  - binary-leavitt-elementary-group-is-simple
---

Inside `H`, the upper-left `EL_4(R)` corner is compressed into itself by the
explicit rank-sixteen Whitehead unit.  The root `e_45(1)` centralizes that
corner, and its transported commutator with `e_12(1)` is `e_02(q)`, where
`q=s_1*t_1`.

The identity `t_1*q*s_1=1` makes `q` full.  Two elementary commutators turn
`e_02(q)` into `e_31(a)` for every `a in R`; Weyl conjugation reaches every
root position.  Hence this one compression defect normally generates `H`.

The group `H` is Kazhdan because the property `(T)` theorem for elementary
groups over finitely generated rings descends from the finite free algebra
onto `R`.  Ordinary normalized-Hilbert--Schmidt transport therefore makes
the compression defect, hence all of `H`, tracially trivial in every
operator-norm asymptotic representation.

If a corona homomorphism had nontrivial image, the Kazhdan fixed-space
projection of that image would have a nonzero invariant complement.  Lift
that complement to asymptotically invariant matrix corners and give each
corner its own normalized trace.  Kazhdan spectral gap forces one fixed
generator to stay a positive Hilbert--Schmidt distance from the identity on
these corners, while defect normal generation forces every element to tend
to the identity there.  This contradiction kills every corona image, so
`Rad_MF(H)=H`.

The preceding simplicity theorem applies at rank sixteen.  The group cannot
be finite: a nontrivial finite group is MF, whereas every MF-target map from
`H` is trivial.  An infinite nonabelian simple group has trivial center and
is ICC.  Indeed, a nontrivial finite conjugacy class would give a proper
finite-index centralizer; the core of that centralizer would be a
finite-index normal subgroup, contradicting simplicity and infinitude.
