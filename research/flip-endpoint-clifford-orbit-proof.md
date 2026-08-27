---
rg: 2
id: flip-endpoint-clifford-orbit-proof
kind: route
title: Apply Clifford orbit theory to the branch pair over the endpoint kernel
target: flip-endpoints-cancel-schur-current
requires:
  - schur-child-center-sign-flip-is-group-automorphism
  - oriented-schur-child-branching-identity
---

Because `C_f` is normal of index two in `R_f`, for every `E` containing
`eta` the subgroup `K=E intersect C_f` is normal in `E`, and conjugation by
`eta` acts on `K` as `theta`.  Let `rho` be any finite-dimensional
representation of `E`.  If `tau` is an irreducible `K`-type occurring in
`rho|K`, then the `eta` image of its isotypic space is the isotypic space for
`tau composed with theta`.  Since `eta` is unitary and invertible, these two
spaces have equal dimension and hence equal multiplicity.

Apply this to the restrictions of the two corrected child types.  If their
`K`-isotypic decompositions coincide, no functional on `K` distinguishes the
two branches.  Otherwise their distinguishing constituents lie in nontrivial
`theta`-orbits, and the preceding paragraph forces every antisymmetric
multiplicity functional on those orbits to vanish in `rho|K`.

Equivalently, Clifford theory for the normal inclusion `K normal E` packages
each two-element orbit `{tau,tau composed with theta}` into an induced
`E`-module.  Counting the two `K` constituents gives the Schur restriction
factor two, while counting the resulting `E`-module gives one object with
twice the dimension.  This is precisely the Morita cancellation computed
for the minimal `D_8` endpoint, and the argument is unchanged after adjoining
any additional selector-dressed elements.  Thus every intermediate endpoint
in `(FCE1)` cancels the oriented current.
