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
