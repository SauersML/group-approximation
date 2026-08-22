---
rg: 2
id: rstar-fano-ghost-affine-hull-proof
kind: route
title: Translate away the ghost and use the four-point cap bound in the Fano plane
target: rstar-fano-ghost-affine-hull-criterion
requires: []
---

Translation by `g` maps the odd affine hyperplane `H` to its direction
space `V` and maps the omitted ghost to zero.  Over `F_2`, zero belongs to
the affine hull of `T` exactly when an odd subset of `T` has xor zero.
A three-point such subset is precisely a Fano line.

Conversely, a line-free subset `T` has size at most four.  Indeed, fixing
`u in T`, the two sets `T\{u}` and `u+(T\{u})` are disjoint subsets of the
six points `V\{0,u}`; an intersection would give a line.  Hence
`2(|T|-1)<=6`.  An odd zero-xor subset of a line-free `T` would consequently
have size one or three, both impossible.  This proves `(RFG3)--(RFG4)`.
The explicit closure failures in `(RFG5)` verify every non-Schaefer case.
