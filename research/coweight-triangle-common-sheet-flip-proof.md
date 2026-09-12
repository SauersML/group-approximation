---
rg: 2
id: coweight-triangle-common-sheet-flip-proof
kind: route
title: Telescope the three coweight flips around the odd triangle
target: coweight-triangle-charges-every-common-sheet-flip
requires:
  - two-denominator-edges-retain-the-exact-two-sheet-atlas
---

The denominator matrices in `(CTA1)` commute and their product is one.
Equivalently, `d_31=h^(-1)` and the word is the torus closure
`h^(-1)d_12d_23` already isolated in
`two-torus-closures-detect-denominator-multiplicity`.
Follow an arbitrary point around the triangle

```text
omega -> d_31 omega -> d_23 d_31 omega
      -> d_12 d_23 d_31 omega=omega.                    (CTQ1)
```

If all three transitions reverse the Boolean label, the final label is the
opposite of the initial label, contradicting the last equality.  Hence one
of the three transitions fails to flip at every point.  Uniform measure is
invariant under each permutation, so averaging the three failure indicators
gives

```text
delta_12+delta_23+delta_31>=1.                           (CTQ2)
```

The maximum is at least `1/3`.  Sharpness is witnessed on three disjoint
copies of `Z/2`: on copy `r`, direction `r` is the identity and the other
two directions are the flip.  The permutations commute, their product is
one, and each direction fails on exactly one of the three copies.

For the matrix form, write `alpha_r=Ad(U_r)` and
`W=U_12U_23U_31`.  Conjugation commutes with complementation and is an
`L^2` isometry.  Successively replace the three transported copies of `P`
by their intended complements.  Word telescoping gives

```text
||alpha_12 alpha_23 alpha_31(P)-(1-P)||_2
 <=epsilon_12+epsilon_23+epsilon_31.                    (CTQ3)
```

On the other hand,

```text
||alpha_12 alpha_23 alpha_31(P)-P||_2
 =||W P W^*-P||_2
 <=2||W-1||_2=2 eta.                                   (CTQ4)
```

Since `(2P-1)^2=1`, one has `||P-(1-P)||_2=1`.  The
triangle inequality applied to `(CTQ3)--(CTQ4)` proves `(CTA7)`.  If
`eta=0`, then `sum epsilon_r>=1`; hence the maximum is at least `1/3`, and
Cauchy--Schwarz gives `sum epsilon_r^2>=1/3`.

The required claim says more than this parity estimate only in locating the
obstruction.  That location follows from
`two-denominator-edges-retain-the-exact-two-sheet-atlas` and the explicit
away-from-`p` evaluation in
`two-denominator-edges-and-coweight-triangle-proof`: every local overlap and
commutation law survives, while the triangle word evaluates to the sheet
flip.
