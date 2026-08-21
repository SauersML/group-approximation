---
rg: 2
id: affine-leavitt-steinberg-mark-is-fd-invisible
kind: claim
title: A finitely presented affine-Leavitt Steinberg group has a nontrivial active word invisible in every exact matrix representation
distinct_from:
  steinberg-cover-fd-triviality: that uses simplicity of the full binary Leavitt algebra to kill every root and every exact finite-dimensional representation; this relative envelope kills only the designated affine active root and may retain the complementary packet sectors.
  schur-toeplitz-root-mark-is-fd-invisible: that uses direct finiteness of a finite Toeplitz coefficient quotient; this uses the one-to-two active module law in a relative Leavitt corner and requires no HNN stable letter.
  affine-active-corner-has-faithful-binary-leavitt-envelope: that is the coefficient-algebra branching theorem; this compiles it into one ordinary finitely presented property-T group and one group word.
---

**ESTABLISHED.**

Let

```text
R_A=L_A(k[C_aff]),       Gamma_A=St_5(R_A),
w_A=x_12(A).                                                (ALS1)
```

Then `Gamma_A` is a finitely presented property-`(T)` group, `w_A!=1`, and
every finite-dimensional unitary representation

```text
rho:Gamma_A->U(d)                                           (ALS2)
```

satisfies

```text
rho(w_A)=1.                                                 (ALS3)
```

Finite presentability follows from the Krstic--McCool theorem for `St_n(R)`
when `n>=4` and `R` is finitely presented.  Property `(T)` follows from the
Ershov--Jaikin-Zapirain theorem for Steinberg groups over finitely generated
associative rings.  Both apply at rank five.

The word is nontrivial because the standard map to `EL_5(R_A)` sends it to
the nonidentity matrix `I+AE_12`, and `A!=0` by the faithful envelope.

For `(ALS3)`, every root subgroup is an elementary abelian `p`-group, where
`p=char(k)`.  Its image in `U(d)` is finite.  Intersect the kernels on the
twenty root subgroups and let `I` be the two-sided coefficient ideal they
generate.  The quotient `R_A/I` is a finite ring, and Steinberg commutators
with spare indices put every `x_ij(I)` in `ker(rho)`.  The relative Leavitt
relations survive in `R_A/I`; finiteness forces the image of `A` to vanish by
the cardinal/module form of `(ALE3)`.  Thus `A in I`, proving `(ALS3)`.

This closes the exact local S3/affine multiplicity-return obstruction:

```text
one active packet copy -> two returned active copies                 (ALS4)
```

is now realized inside a faithful finitely presented ordinary group-word
system, with marked completeness and exact finite-dimensional collapse.
It does **not** prove `Gamma_A` nonhyperlinear.  The remaining theorem is a
normalized-HS analogue of `(ALS3)`: sufficiently accurate finite-dimensional
almost representations must make `w_A` small.  Exact root-kernel
intersection is dimension-dependent, and HS-small error need not be
rank-small.

## Attempts

- **Exact coefficient decoding succeeds.**  The finite root images give the
  finite quotient used above; no selector reset, HNN return, or finite packet
  commutant-density hypothesis remains.
- **Approximate coefficient decoding remains open.**  Rounding any fixed
  finite root table does not control the rank of the discarded subspace as
  the coefficient window grows.  This is the same metric conversion isolated
  by `hs-steinberg-root-kernel-is-linear-sofic`, now isolated in the strictly
  smaller interface `affine-leavitt-steinberg-hs-coefficient-decoder`, with
  the stronger local Leavitt equation available after decoding.
- **The post-decoding HS payment is solved.**
  `approximate-relative-leavitt-cell-kills-active-trace` proves the
  dimension-free endpoint `tr(P)<=3epsilon` from only the two diagonal
  inverse relations and the range-sum relation.  Therefore no further
  multiplicity integrality or recurrence is needed after coefficient
  extraction; the whole analytic gap is the root-to-coefficient decoder.
- **No trace-functorial overclaim.**  The infinite faithful coefficient model
  is properly infinite and need not carry a finite trace.  The group regular
  representation sees `w_A!=1` but does not extend to a representation of
  the coefficient algebra `R_A`; therefore `(ALE3)` is not asserted for all
  tracial group representations.
