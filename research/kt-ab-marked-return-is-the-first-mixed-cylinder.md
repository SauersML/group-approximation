---
rg: 2
id: kt-ab-marked-return-is-the-first-mixed-cylinder
kind: claim
title: One Gamma root conjugated by an A,B word is the first decisive lamp cylinder
distinct_from:
  kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath: That proves every cylinder confined to the external A,B orbit has canonical permutation models; this identifies the first mixed cylinder outside that orbit and writes its actor as an explicit Gamma--A,B word.
  two-site-a5-center-classicalization: That asks for the unitary-to-permutation transfer on the marked pair; this shows exactly how its marked mover lies in the two-compressor presentation and that no larger lamp family is needed after classicalization.
  two-site-a5-center-has-exact-boundary-countermodel: That gives a generic finite boundary countermodel to fixed-pair coupling composition; this identifies the arithmetic mixed relation which a positive proof would have to use to defeat that countermodel.
---

**ESTABLISHED.**  In the `d=3` pair, choose

```text
r=e_12(x_1) in Gamma,
L=[[-1, 0, 0],
   [-1,-1, 0],
   [-1, 0, 1]] in SL_3(Z)=<A,B>.                       (KMR1)
```

Then `det(L)=1`, `L e_1=-(1,1,1)`, and monomial conjugation gives

```text
h=L r L^(-1)=e_12((x_1 x_2 x_3)^(-1)).                (KMR2)
```

Thus the Kun--Thom marked pair

```text
p=Gamma,                   q=h Gamma                  (KMR3)
```

is already named by the two compressor generators `A,B` and one polynomial
root `r`.  It is not contained in the regular external orbit
`<A,B> Gamma`: the elementary Laurent component of `h` is nontrivial.

After a common actor table or invariant diagonal has been extracted, the
two lamp coordinates in `(KMR3)` are enough for the terminal permutation
contradiction.  For binary lamps their exclusive-or projection has canonical
trace `1/2`; for the rational five-dimensional `A5` center it has trace
`35/72`.  The finite actor word for `h` transports the first coordinate to
the second, while `two-point-approximation-fails` forbids an approximately
multiplicative finite actor table retaining their distinction.

Consequently the smallest live cylinder interface for the explicit
two-compressor seam is not a large `A,B` orbit PVM.  It is the two-site PVM
at `(Gamma,hGamma)` together with the mixed word `(KMR2)` and the Kazhdan
stabilizer rows for `Gamma`.  Turning that PVM into a common actor-normalized
diagonal is exactly `two-site-a5-center-classicalization` (or the binary
analogue).  Individual covariance of the pair is insufficient by
`two-site-a5-center-has-exact-boundary-countermodel`; a proof must use the
arithmetic return `(KMR2)` to control the boundary multiplicity cocycle.

DERIVATION
kt-ab-marked-return-cylinder-proof
