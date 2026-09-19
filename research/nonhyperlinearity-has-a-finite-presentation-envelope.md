---
rg: 2
id: nonhyperlinearity-has-a-finite-presentation-envelope
kind: claim
title: Every nonhyperlinear group has a finitely presented nonhyperlinear partial-table envelope
distinct_from:
  hyperlinear-radical-presentation-compactness: that characterizes collapse of one word in a fixed finite presentation; this extracts a new finite presentation from an arbitrary nonhyperlinear group's bad multiplication window.
  effective-corner-host-higman-promotion: that uses effectivity and Higman embedding to promote a recursively presented corner host; this needs neither recursive presentation nor an embedding theorem.
  finite-support-corner-localizes-obstruction: that localizes a given algebraic corner map to a finitely generated support subgroup; this works directly from any forbidden hyperlinear window and produces a finite presentation.
---

**ESTABLISHED.**  If a discrete group `G` is nonhyperlinear, then some
finitely presented group `K` is nonhyperlinear.

Indeed, failure of the finite-window definition supplies a finite set
`F subset G` and `epsilon>0` for which no matrix microstate realizes the
visible products and separates the distinct elements of `F`.  Introduce one
generator `x_g` for each `g in F`, impose `x_1=1` when applicable, and impose
only

```text
x_g x_h=x_k whenever g,h,k in F and gh=k in G.          (FPE1)
```

The resulting group `K` is finitely presented and maps to `<F> <= G` by
`x_g |-> g`.  Hence distinct named elements of `F` remain distinct in `K`.
If `K` were hyperlinear, apply a sufficiently accurate microstate to the
finite subset containing the named elements and their pairwise differences.
Its restriction to the names would realize the forbidden window in `G`, a
contradiction.

Thus allowing an arbitrary, infinitely generated, or infinitely presented
candidate gives no advantage for the existence question:

```text
some group is nonhyperlinear
iff some finitely presented group is nonhyperlinear.    (FPE2)
```

This does not make a recursive diagonal automatically finite.  It says that
if its limit really is nonhyperlinear, a finite bad window already contains
the obstruction and its partial-table presentation is already a witness.
