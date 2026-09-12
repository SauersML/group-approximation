---
rg: 2
id: binary-jacobson-mf-radical-dichotomy-proof
kind: route
title: Separate Laurent matrices by finite fields and use simplicity of the finitary kernel
target: binary-jacobson-mf-radical-dichotomy
requires:
  - binary-jacobson-elementary-mark-is-finite-quotient-invisible
  - binary-jacobson-head-retaining-homomorphisms-are-faithful
  - binary-jacobson-steinberg-cover-is-elementary
---

The exact symbol sequence and simplicity of `L` are supplied by the first
prerequisite.  The quotient `Q_0` is residually finite directly.  Given a
nonidentity Laurent matrix `g`, choose a nonzero Laurent-polynomial entry of
`g-I`.  Some finite-field specialization of `z` to a nonzero algebraic
element keeps that entry nonzero.  Entrywise specialization then gives a
finite general-linear quotient separating `g` from the identity.  Restrict
it to `Q_0`.

The quotient map `E->Q_0`, followed by its faithful norm-corona model, shows
`Rad_MF(E)<=L`, proving `(JRD1)`.  The MF radical is normal in `E`, hence its
intersection with the simple subgroup `L` is either `1` or `L`; because it
already lies in `L`, this proves `(JRD2)`.

For a countable group, trivial MF radical gives one faithful norm-corona
model by enumerating the nonidentity elements, choosing an MF-target map
separating each one, and diagonally reblocking their matrix models.  Thus the
first alternative is precisely operator-MF.  In the second alternative every
MF-target map kills `L` by the definition of the radical and therefore
factors through `Q_0`; conversely `Q_0` itself is residually finite and MF.

Finally the second and third prerequisites identify the Steinberg group with
`E` and show that any homomorphism retaining the head is faithful.  This
proves both equivalences in `(JRD3)`.
