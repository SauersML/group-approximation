---
rg: 2
id: atlas-psl5-repeated-natural-collision-collapse
kind: claim
title: Every repeated natural PSL5(2) carrier collapses the marked collision involution
distinct_from:
  atlas-q1920-psl5-double-natural-module-has-no-collision-seam: that exhausts the finite centralizer at multiplicity two; this treats every multiplicity at once through a universal noncommutative coefficient algebra.
  atlas-q1920-marked-simple-factor-is-at-least-ten-million: that is a finite census of simple hosts below an order bound; this excludes an infinite family of arbitrarily large simple hosts uniformly.
  atlas-cfsg-family-split-does-not-finitize-a8-carriers: that warns that repeated-block simple hosts defeat a finite CFSG sieve; this closes the corresponding repeated-natural family for the Q1920 collision marking.
---

Let `W` be the natural five-dimensional `F2[PSL5(2)]` module, restricted
along any of the marked embeddings

```text
Q/Z(Q)=2^4:A5 --> PSL5(2).
```

For every `m>=1`, let `Q/Z(Q)` act diagonally on `W^m`.  If an operator `c`
centralizes `A=<r,u>` and satisfies

```text
c^2=1,
(c t)^3=1,
t c s c t^-1 c s t c=1,                                (PSL5M-1)
```

then `c=1`.  In particular the protected collision vertex
`<t,s,c>~=S4` cannot occur.  Thus no block-repeated natural embedding in any
`PSL_(5m)(2)=GL_(5m)(2)` is a marked full-Q carrier.

The result covers both Q markings, both ambient embedding classes in
`PSL5(2)`, and all four normalizer-orbit twists, at every multiplicity.  It
does not classify arbitrary modular representations of `Q/Z(Q)` or embeddings
of `Q` in other classical families.

## Attempts

The multiplicity-two census saw zero candidates but could not rule out a
disconnected solution component appearing later.  Passing to five *freely
noncommuting* coefficient variables removes the dimension bound.  The exact
two-sided Groebner basis is the identity ideal in every marked slice, so
there is no later component to appear.
