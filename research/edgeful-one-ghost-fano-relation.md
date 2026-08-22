---
rg: 2
id: edgeful-one-ghost-fano-relation
kind: claim
title: A fixed NP-hard one-ghost relation has Fano-cap soundness and honest Hamming edges
distinct_from:
  rstar-fano-ghost-affine-hull-criterion: that uses the full odd-four-parity hyperplane, whose honest points have no Hamming-distance-one edges; this uses a weight-two parity check and keeps the same abstract Fano geometry.
  culf-mastel-rstar-fixed-language-gap-is-published: that specializes the published family to the non-TVF relation R-star; this identifies a different NP-hard Boolean language and explicitly records that it is not non-TVF.
---

Put

```text
H_edge={x in F_2^4:x_1+x_2=1},
g=1000,
R_edge=H_edge\{g}.                                      (EOF1)
```

Thus

```text
R_edge={1001,1010,1011,0100,0101,0110,0111}.            (EOF2)
```

The one-relation Boolean language `{R_edge}` is NP-complete.  It is neither
zero-valid nor one-valid.  The following explicit witnesses exclude all
four remaining Schaefer classes:

```text
1001 AND 0100 = 0000 notin R_edge,                       (Horn)
1001 OR  0100 = 1101 notin R_edge,                       (dual Horn)
Maj(1001,1010,0100)=1000 notin R_edge,                   (bijunctive)
1001 XOR 1010 XOR 1011=1000 notin R_edge.                (affine)
```

Moreover `Aff(R_edge)=H_edge`, and translation by `g` identifies

```text
R_edge+g = V\{0},   V={v:v_1+v_2=0} isomorphic to F_2^3. (EOF3)
```

Consequently, for every `S subseteq R_edge`,

```text
Aff(S) subseteq R_edge
 iff S+g contains no projective line in PG(2,2).          (EOF4)
```

The same seven-line Fano-cap support certificate used for `R_*` therefore
works verbatim after relabeling the seven points.  In particular, a perfect
context model supported on a cap can be affine-linearized without admitting
the unique ghost.

Unlike `R_*`, this coordinate realization has honest Hamming-distance-one
edges.  In fact every coordinate can be preserved by such an edge:

```text
0100 -- 0101     differs only in coordinate 4,
0100 -- 0110     differs only in coordinate 3.           (EOF5)
```

The first edge agrees in coordinates `1,2,3`, and the second agrees in
coordinates `1,2,4`.  Hence for every prescribed coordinate `x` there are
distinct `a,b in R_edge` which agree at `x` and differ in exactly one other
coordinate.

There is a precise tradeoff.  `R_edge` is two-variable falsifiable: its
projection to coordinates `(1,2)` is only `{10,01}`.  Thus the non-TVF
one-row commutativity-gadget shortcut used for `R_*` is unavailable.  Its
NP-hardness still places it in the Boolean fixed-language side of the
Culf--Mastel theorem, but any use requiring their separate non-TVF clause
must provide another commutativity gadget.  This claim supplies the local
Fano and escape geometry, not a cap-supported HALT model.
