---
rg: 2
id: endpoint-whitehead-signed-source-intersection-proof
kind: route
title: Compute the endpoint-moved signed Hecke intersection and its exact Grams
target: endpoint-whitehead-signed-source-has-only-relative-hecke-overlap
requires:
  - endpoint-detector-cell-retains-coboundary-gauge
  - finite-character-hecke-intersection-formula
---

Write `p` for the spare endpoint and abbreviate

```text
e=e_m,       f=e_(m+1),
c=s_(0^(m+1))t_(0^m),       d=s_(0^m)t_(0^(m+1)).
```

On the ordered coordinates `(p,r)`, the endpoint Whitehead is the
involution

```text
W=[[1-f,c],[d,1-e]],             cd=f,       dc=e.       (1)
```

Let `g in L_0`.  Its actor matrix is constant, its `p` row and column are
those of the identity, and its `r,r` entry is one.  If `u_j` is its
`r,j` entry and `v_i` its `i,r` entry, direct block multiplication gives

```text
(WgW)_(p,j)=c u_j,                (WgW)_(i,p)=v_i d.     (2)
```

Both `c,d` are nonzero: otherwise `cd=f` or `dc=e` would vanish, contrary
to prefix cancellation.  Since `u_j,v_i in F_2`, equation `(2)` has no
spare-coordinate entries exactly when every `u_j,v_i` vanishes.  In that
case `g` is the identity on coordinate `r`, commutes with `W`, and
`WgW=g`.  This proves the description of `K_r` and equality of the two
characters on it.

Closing the ten displayed transvections of `L_0` over `F_2` and imposing
this row-and-column condition gives `(EHS2)`.  The reproducible audit also
checks the stated generating sets and the balanced character restrictions.
Because `W` is disjoint from the endpoints of `z`, it commutes with `z`,
which proves `(EHS3)`.

Now `Q'=WQW` and `W^2=1`, so

```text
Q'WQ=WQ,       (WQ)^*(WQ)=Q,       (WQ)(WQ)^*=Q'.      (3)
```

This proves the full source and range Grams.  Applying the finite-character
intersection formula to the two groups of order `8192` gives

```text
tau(QQ')=|K_r|/8192^2.
```

Since the canonical regular trace has `tau(Q)=1/8192`, substitution of
`(EHS2)` proves `(EHS5)`.

For the profile fence, the same enumeration computes the characters of
`L_0`.  The character negative only on `4->2` is trivial on `K_2`, and the
character negative only on `5->4` is trivial on `K_4`.  Call the applicable
one `xi_r`.  The two diagonal characters agree on `K_r`, so the displayed
swap commutes with every `K_r` operator and realizes every relation used in
the intersection calculation.  Character orthogonality gives `(EHS6)`.

Finally, source multiplication by `L_0` is scalar on its character
projection.  A signed normalizer acts unitarily on that projection, so two
normalizer-dressed full edges have full cross Gram.  A constant actor word
cannot remove either coefficient in `(2)` from the spare row and column;
therefore it cannot conjugate the moved signed pair back to the original
one.  Applying `W` again is the only supplied return and is the inverse of
the original edge.  This proves the claimed short-word and gauge fence.
