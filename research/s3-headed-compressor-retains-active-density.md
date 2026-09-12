---
rg: 2
id: s3-headed-compressor-retains-active-density
kind: claim
title: Couple the S3 active endpoint algebra to the old commutant of the S3-headed compressor
---

Attach `affine-s3-endpoint-permutes-active-atoms` to the endpoint `D` and
identify its forbidden-point stabilizer with the external `S_3` in
`toeplitz-s3-headed-holonomy-compressor`.  This is not the packet automorphism
group which permutes the three radical charts: that group fixes `K` and does
not permute the three atoms of one active vector.  Add a fixed ordinary-word
coefficient-covariance cell such that every sufficiently accurate marked
matrix microstate with active mass `a` has a subspace

```text
W <= low-commutator space of Lambda,
tr_ad(W)>=a^2/18-C sqrt(E),                               (SHD1)
```

and `W` is the affine-`S_3` invariant multiplicity algebra supplied by
`(ASE4)`.

The covariance must visibly fail in the tensor-decoupled representation: it
is not enough that the packet commute with the external `S_3` or with the
deep tail separately.  An acceptable proof may give a survive-or-recurse
dichotomy, but the recurse branch must use the same residual multiplicity
algebra that erased `(SHD1)` and must retain the oriented one-jump exit.

Once `(SHD1)` holds, the sign-parity implementer copies `W` into an almost
orthogonal excess low-commutator subspace.  Property-`(T)` commutant
no-growth then charges `a^2` to normalized-HS relator energy.

## Attempts

- Bare direct-product placement fails: the universal-lattice factor may act
  irreducibly on every endpoint block and reduce the old commutant to zero
  density.
- `finite-edge-attachments-residual-decouple` proves
  that this failure persists for every attachment made only through the fixed
  affine `S_3` edge: tensoring the endpoint with growing regular finite
  quotients makes the old-commutant density tend to zero while preserving
  active mass exactly.  Therefore the missing covariance relation must
  contain a nontrivial Toeplitz coefficient word outside the edge, or recurse
  in the residual quotient algebra itself.
- `finite-affine-head-cannot-retain-old-commutant-density` gives the exact
  live countermodel: tensor one three-dimensional active affine orbit with
  the regular representations of `EL_r(F_(2^n))`.  Active mass remains one
  while the old-commutant density is `2/(9|EL_r(F_(2^n))|)->0`.
- The pair-permutation `S_3` of the original packet is a chart symmetry, not
  a channel symmetry.  Using it here would not even equalize the three
  coordinates in `(SEA4)`; the affine endpoint extension `(ASE2)` is
  essential.
- The bounded S3 head solves the algebraic chart reset but not this residual
  action.  The live attack is to compile the Toeplitz head matrix units into
  the endpoint Wedderburn coefficients and prove a finite survive-or-recurse
  conditional-expectation inequality.
