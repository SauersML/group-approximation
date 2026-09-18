---
rg: 2
id: binary-leavitt-haar-row-profile-is-not-mf-character-restriction
kind: claim
title: The full Haar row profile is not the restriction of a binary Leavitt Steinberg MF character
distinct_from:
  binary-leavitt-row-dual-ergodic-measure-classification: that asks for all invariant ergodic measures without using their matrix origin; this excludes only full Haar and crucially retains the MF-character and ambient Steinberg hypotheses.
  surviving-leavitt-corona-character-has-infinite-parabolic-orbit: that rules out finite nontrivial character orbits but is compatible with a diffuse Haar spectrum.
---

**OPEN.**  Let `Delta=St_20(L_(F_2)(1,2))` and let `N` be either a full
first-row or last-column abelian root module.  There is no MF character
`chi` of `Delta` satisfying

```text
chi(v)=0                    for every 1!=v in N.       (HRP1)
```

Equivalently, the restriction of an MF character to `N` cannot be the
Fourier transform of Haar measure on `hat N`.

Abstract Haar measure is invariant under the parabolic shear action and is
the restriction of the regular character of `Delta`; thus invariance,
positive definiteness, or exact group relations in a finite von Neumann
algebra cannot prove the claim.  A proof must use the operator-norm matrix
origin together with relations outside the root module.  This is a narrower
form of the unresolved MF-character endpoint, not an independent solution.

## Attempts

Every fixed additive-rank window accepts the Haar profile, and the regular
representation realizes it exactly in a finite von Neumann algebra.  The
finite-orbit theorem also leaves it untouched.  The attack is deferred to a
literal non-diagonal or two-compressor relation that uses operator-norm
matrix origin and has no regular-representation analogue.

The purely character-theoretic part is now exhausted on the parabolic.
`haar-root-character-vanishes-off-parabolic-action-kernel` applies Bessel to
the root-module conjugacy orbit and proves that `(HRP1)` already forces the
regular-character value on every parabolic element whose vertex action is
nontrivial.  It deliberately stops at the action kernel and gives no
finite-matrix contradiction.

The first genuine opposite-root occurrence is also insufficient.
`first-partial-inverse-whitehead-face-has-haar-mf-character` adjoins

```text
omega=x_23(s_0)x_32(t_0)x_23(s_0)
```

to the full row module and identifies a locally finite quotient
`(R,+)^(n-1) semidirect C_2`.  Its exact finite regular models retain the
mark and have Haar restriction on the row.  Thus the relations
`t_0s_0=1`, `s_0t_0=p`, and their shortest opposite-root Whitehead word do
not close `(HRP1)`; at least two noncommuting coefficient occurrences or a
global return are necessary.

Even the complementary Whitehead pair remains finite-type.
`two-whitehead-face-has-haar-mf-character` computes the two actor blocks and
shows that they generate exactly `S_3`; the full face is
`(R,+)^(n-1) semidirect S_3`, locally finite with an exact Haar-row MF
character retaining `z`.  What first escapes this fence is not the two
Whitehead involutions but the individual same-root packet
`x_ij(s_0),x_ij(t_0)` together with the constant coordinate swap:
`leavitt-first-offdiagonal-packet-breaks-locally-finite-amalgam` extracts an
infinite-order prefix shift.  That result breaks the previous locally finite
amalgam proof only; it does not yet exclude a different MF model.

The exact status of that packet is now sharper.
`leavitt-first-offdiagonal-core-is-marked-non-lef` identifies it with an
elementary group over the one-branch algebraic Toeplitz ring and gives a
finitely presented Steinberg cover whose marked defect dies in every finite
quotient.  Thus one raw factor beyond the completed Whitehead involution is
already a genuine finite-table obstruction.  The distinction between LEF
and MF is now load-bearing: operator-norm microstates can still use
rectangular Morita multiplicities, and excluding those is exactly the
unproved root-to-square decoder rather than a further group-normal-form
calculation.

The first explicit **downstairs elementary-group** two-compressor relation
beyond the one-level Haar model is the depth-two split of the marked
off-diagonal root.  With bars denoting elementary images and
`z=x_13(s_1t_1)`, it is

```text
bar(tau_0) bar(z) bar(tau_0)^(-1)
 = (bar(tau_0)^2 bar(z) bar(tau_0)^(-2))
   (bar(tau_1) bar(tau_0) bar(z)
      bar(tau_0)^(-1) bar(tau_1)^(-1)).                (HRP2)
```

This is `(DTS1)` of
`leavitt-two-compressor-depth-two-relation-breaks-hxh-model` specialized to
`z`.  That claim proves that the canonical `H times H` one-level covariance
model, whose trace is Haar on every nontrivial diagonal-stage element, does
not satisfy `(HRP2)`.  This identifies the first explicit off-diagonal test
missed by that model; it does **not** prove that `(HRP2)` excludes arbitrary
MF coordinates.  Nor is equality of the corresponding chosen Steinberg
lifts asserted here: a central Steinberg correction must first be computed
for those literal words.  Even after that lift is verified, a growing
coordinate may realize deeper child trees, so a valid obstruction must still
turn the recursive split into one fixed same-reservoir rank or operator-norm
return.

**Dead (2026-09-18, entropy-measure transplant, swarm-0917-w8-w8-ptm-pull).**
The attempt was to import a measure or entropy invariant of the parabolic
dual action on `(hat N, Haar)`, such as a Rokhlin or sofic entropy, a
Bernoulli fixed-point measure, or a clopen compression, and use it as the
missing non-tracial input.  It dies before any computation, in three places.
1. *Measure data.*  Haar on `hat N` is the restriction of the regular
   character (see the statement above).  So every invariant of the pmp dual
   action of the parabolic, entropy included, is realized by the GNS model
   of the regular character.  Haar invariance also rules out the only
   measure-level compression: an automorphism `g` cannot map a nonempty
   clopen `D` of `hat N` onto a proper clopen subset of `D`, since the
   difference would be a nonempty clopen set of Haar measure `0`.
2. *The operator-norm substitute through stable finiteness.*  Every trace
   `tau` on a unital C*-algebra `A` vanishes on the closed ideal generated
   by `e-f`, whenever `e` and `f` are projections in `M_n(A)` with
   `e ~ f <= e`.  This is because `tau(e-f)=0` and
   `tau(x(e-f)x*) <= ||x||^2 tau(e-f)`.  So proper isometries in matrices
   over `C*(Delta)` never separate MF characters from other characters, and
   the finiteness of the corona `prod M_d / sum M_d` constrains no trace.
   This is the group-level form of item 4 of
   `jacobson-boundary-amalgam-gap-is-a-reduced-mf-gate`.
3. *Routing.*  `leavitt-mf-survivor-yields-jacobson-regular-character`
   (commit 2a267fd54) now reduces the Leavitt MF-radical lane to the regular
   character of `EL_5(J)`.  A measure-theoretic proof of `(HRP1)` would
   therefore have to beat the same Kazhdan-free fence at
   `jacobson-regular-character-not-mf-without-property-t`, where it is
   stated in its cleanest form.
