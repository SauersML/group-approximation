---
rg: 2
id: agent-free-compressor-authenticated-corner-pays-hs
kind: claim
title: An authenticated named packet corner pays the HNN rank gap dimension-uniformly
distinct_from:
  finite-group-multiplicity-mismatch-pays-hs-energy: That is the general finite-group intertwiner estimate; this specializes it to `(BCL0)--(BCL2)` and identifies the sole input that the Steinberg decoder must extract.
  agent-free-compressor-minimal-nonretractive-corner: That proves exact coefficient-module vanishing; this gives the normalized-HS robust inequality for an approximately authenticated physical corner.
  hs-steinberg-bcs-corner-kernel-is-linear-sofic: That asks for coefficient reconstruction from root microstates; this proves everything after the physical named-packet corner has been reconstructed.
---

Fix the finite packet inclusion `A_f<B_f`, its generators `b_i`, child words
`a_i`, and a finite type projection `e` on which

```text
tr(e e_A)-tr(e e_B)>=gamma tr(e)                       (ACP1)
```

for a fixed `gamma>0`.  There is a constant `C`, depending only on this
finite packet and the fixed words, with the following property in every
matrix dimension.

Suppose rounded unitary matrices `B_i,U_i,T` and a projection `e` satisfy:

```text
e approximately reduces every B_i,U_i and T,
||(U_i-B_i)e||_2<=delta,                               (ACP2)
||T U_i T^(-1)-U_(alpha(x_i))||_2<=epsilon,            (ACP3)
||U_(alpha(x_i))e-A_i e||_2<=C_0 delta.                (ACP4)
```

Here the `B_i` form an exact representation of `B_f` on `eH`, the `A_i`
are its exact restricted `A_f` words, and all reduction errors are included
in `delta`.  Then

```text
gamma tr(e)<=C(delta+epsilon).                         (ACP5)
```

Thus a positive-density authenticated `(BCL0)` corner cannot coexist with
vanishing HNN defect.  No full coefficient quotient, infinite-kernel
argument, or self-copy fixed-space theorem is needed after `(ACP2)` is known.

Applied to the Steinberg route, `(ACP3)--(ACP4)` are fixed-word consequences
of `(BCL1)--(BCL2)`.  The tempting remaining operation would be:

```text
root/BCS spectral mass
   -> one projection e satisfying the named identification `(ACP2)`. (ACP6)
```

However, `agent-free-compressor-named-row-retains-complement-gauge` proves
that `(ACP6)` is false as an isolated lemma even after `(BCL0)` and all
rank-`N` Steinberg identities are imposed.  Thus this claim is a robust
endpoint, not a sequential route: a surviving proof must derive the corner
identification and charge its HNN rank mismatch in one simultaneous
inequality.  Root support, kernel rows, or HNN covariance considered before
that simultaneous payment retain the complement gauge.
