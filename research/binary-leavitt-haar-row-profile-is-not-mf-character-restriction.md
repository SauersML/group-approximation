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
