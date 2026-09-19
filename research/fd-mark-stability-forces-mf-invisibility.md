---
rg: 2
id: fd-mark-stability-forces-mf-invisibility
kind: claim
title: Point-norm stability at one marked element already carries that element into the MF radical
distinct_from:
  matricial-stability-identifies-radicals: that hypothesizes Dadarlat point-norm stability at EVERY element of the group and computes the whole radical; this hypothesizes it at a SINGLE marked element and concludes about that element only, which is the weakest stability input any one-mark non-MF argument can consume.
  map-matricial-stability-non-mf: that assumes minimal almost periodicity together with full matricial stability, so its finite-dimensional residual is the whole group; this assumes neither, only that one element is finite-dimensionally invisible and that the approximants can be repaired at that one element.
  corona-defect-is-not-uniform: that is the negative calibration, recording that corona lifts supply pointwise but never uniform defect and so killing every Ulam-type route; this is the positive consequence of the pointwise hypothesis that survives that calibration, and is stated in exactly the point-norm form the calibration leaves available.
  full-mf-radical-uniform-asymptotic-collapse: that is the equivalence between total MF radical and pointwise triviality of every asymptotic representation, a statement about the whole group; this is a one-element transfer that needs no totality and no uniformity.
---

**ESTABLISHED.**  For a countable group `G` write

```text
Rad_fd(G) = intersection of ker(pi) over all finite-dimensional unitary pi,
Rad_MF(G) = intersection of ker(Theta) over all homomorphisms
            Theta : G -> U(Q),  Q=prod_n M_(d_n)/sum_n M_(d_n).
```

Call `G` **fd-stable at the mark `w`** if for every point-norm asymptotic
homomorphism `phi_n : G -> U(d_n)` -- not necessarily separating -- there are
genuine homomorphisms `pi_n : G -> U(d_n)` with

```text
||phi_n(w)-pi_n(w)||_op -> 0.                              (MRK1)
```

Nothing is asked at any other element of `G`.  Then

```text
w in Rad_fd(G)  and  G fd-stable at w   ==>   w in Rad_MF(G).  (MRK2)
```

Consequently, if some `w != 1` is finite-dimensionally invisible and `G` is
fd-stable at `w`, then `G` is **not MF**; and if such `w` normally generate
`G`, then `Rad_MF(G)=G`, since the MF radical is an intersection of kernels
and hence normal.

## Why the one-element form is the right statement

Every non-MF argument in this program is aimed at a single marked element,
and then globalized by normal generation.  Full matricial stability --
`matricial-stability-identifies-radicals`, and Dadarlat's hypothesis as
recorded in `dadarlat-matricial-stability-obstruction` -- repairs the
approximants at *every* element, which is far more than the endpoint
consumes.  `(MRK2)` isolates exactly what is consumed.

This matters because the wall recorded on `map-matricial-stability-non-mf`
is that stability is unproved for every candidate here.  A one-element
stability statement is a strictly smaller thing to prove than a group-wide
one, so the wall is lowered even though it is not removed.  The same
observation is what makes
`authenticated-coarse-fine-return-forces-mf-collapse` a viable substitute:
that node replaces `(MRK1)` at the mark by a finite-coordinate return row,
which is a local and syntactic condition rather than a global analytic one.

## What it does not do

It does not produce a stable group.  `bare-self-copy-mf-calibration` shows
that finite-dimensional invisibility alone is decisively insufficient: for
`G=<a,t,p | t a t^-1=a^2, [p,a^2]=1>` and `w=[p,a]`, every exact
finite-dimensional representation kills `w`, yet `G` is operator-MF and a
norm-matrix-corona representation keeps `w` nontrivial -- and in the escaping
matrix model the parent and child generated C*-algebras are even equal.  So
`(MRK1)` is not decoration; some hypothesis of that strength is forced.
