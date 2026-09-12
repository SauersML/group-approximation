---
rg: 2
id: atlas-gl6-repeated-affine-collision-collapse
kind: claim
title: Every repeated homogeneous-affine GL6(2) carrier collapses the marked collision involution
distinct_from:
  atlas-psl5-repeated-natural-collision-collapse: that excludes repeated five-dimensional modules of the central quotient Q/Z(Q); this excludes the faithful six-dimensional homogeneous affine modules of Q itself.
  atlas-q1920-agl5-has-no-collision-involution: that works inside the fixed affine normalizer on one five-dimensional affine space; this treats arbitrary multiplicity and allows every A-central block operator in GL_(6m)(2).
  atlas-q1920-marked-simple-factor-is-at-least-ten-million: that is a bounded census of simple hosts; this excludes the infinite family GL_(6m)(2)=PSL_(6m)(2) uniformly in m.
---

Let `Q=2^5:A5` be either of the two faithful marked order-1920 quotients of
the large rectangle, let `V=O_2(Q)`, and let `K` be any `Q`-conjugacy class
of complements to `V`.  There are exactly four such classes.  Write `H_K`
for the faithful six-dimensional homogeneous linearization over `F2` of the
affine action `Q` on `Q/K`.

For every `m>=1`, let `Q` act diagonally on `H_K^m`.  If an operator `c`
centralizes `A=<r,u>` and satisfies

```text
c^2=1,
(c t)^3=1,
t c s c t^-1 c s t c=1,                              (GL6M-1)
```

then `c=1`.  Hence the protected collision subgroup `<t,s,c>~=S4` cannot
occur.  No block-repeated homogeneous-affine embedding in
`GL_(6m)(2)=PSL_(6m)(2)` is a marked full-Q carrier.

The audit covers both faithful Q markings and all four complement classes
for each marking.  It therefore includes every twist of these affine actions
by an automorphism of the marked Q: precomposition moves the origin
stabilizer to another complement class.  It does not classify arbitrary
`F2[Q]` modules, mixtures of inequivalent modules, or other classical
families.

## Attempts

The fixed `AGL5(2)` centralizer census could not exclude a collision operator
that mixes repeated affine copies.  Freely noncommuting multiplicity
coefficients encode all such mixing at once.  In every one of the eight
marked slices, the exact two-sided Groebner basis forces every coefficient to
its identity value.
