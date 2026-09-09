---
rg: 2
id: directed-monomial-incidence-proves-intertwiner-rigidity
kind: route
title: Compare the incident quadratic monomials in each finite output row
target: quadratic-intertwiners-cannot-scalarize-triangular-feedback
requires: []
artifacts:
  - research/artifacts/gottschalk-directed-quadratic-intertwiner-rigidity-2026-09-08.md
---

For a nonzero row ell of a continuous linear intertwiner, let eta
be its successor row. Intertwining gives ell(Qx)=ell(x)eta(x).
Evaluating on source unit vectors makes their supports disjoint.
An internal directed edge of supp(ell) would then occur only on
the left, so no such edge exists. Each supported coordinate has
exactly one incident monomial on the left, whereas the product
on the right joins it to every coordinate in supp(eta). Hence
eta is its single successor coordinate. Injectivity of the source
permutation forces ell itself to be a single coordinate.

This row argument only requires that the source permutation have
no cycles of length one or two. On finite target cycles, nonzero
rows propagate around the whole cycle. For affine maps, the
constant part is fixed by Q. A target triple with constant part
111 has no linear contribution, since the sole preimage of 111
under Q is 111. The other triples use the linear classification.

The triangular rule fixes all second-track coordinates and fixes
no first-track coordinate on every input. Injective copy/constant encodings
retain a nonempty proper fixed-coordinate set. An equivariant map
on an invariant code forces this set to be invariant under the
target action, contradicting transitivity.

For a separate constraint, every fiber Q^-1(q) with q a single
source unit vector has trivial translation stabilizer. If x+A Q
commutes with Q, it translates this fiber into itself by Aq,
forcing Aq=0. This for all unit vectors, together with continuity,
forces A=0. A controlled triple rotation on C_3 x C_2 supplies
a nonlinear reversible Q-intertwiner outside that feedback class.
