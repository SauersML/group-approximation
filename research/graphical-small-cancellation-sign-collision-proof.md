---
rg: 2
id: graphical-small-cancellation-sign-collision-proof
kind: route
title: Put one long aperiodic X word and one long aperiodic Z word around the two sign letters
target: gsc-does-not-separate-sign-double-cosets
requires: []
---

Choose alphabets `D_X,D_Z` with at least two letters each.  For arbitrarily
large `L`, choose cyclically reduced words

```text
u_L in F(D_X),                 v_L in F(D_Z)
```

so that every repeated subword among the cyclic conjugates of `u_L` and
`v_L` has length `o(L)`.  Such words exist by the usual counting argument
(equivalently, choose aperiodic random reduced words and retain one good
choice).  Put

```text
r_L = u_L p_0 v_L p_1^-1.                                      (1)
```

The four alphabets are disjoint and `p_0,p_1` occur only once.  Hence every
piece of the symmetrized relator `(1)` lies inside one of the two aperiodic
blocks, up to a bounded endpoint contribution.  Taking `L` large makes the
one-relator presentation satisfy `C'(lambda)`.

But `(1)` gives

```text
p_1 = u_L p_0 v_L,
```

so `p_1` belongs to `<D_X> p_0 <D_Z>`.  Since it also belongs to
`<D_X> p_1 <D_Z>`, their intersection is nonempty.  Viewing `(1)` as the
label of one cycle gives the graphical version.

Product-refining the labels by their edge types cannot repair the example:
the labels already remember those types exactly.  Any positive incidence
theorem must exclude the mixed two-sign contour `(1)` and all diagrammatic
composites of that contour by a genuine relative argument.
