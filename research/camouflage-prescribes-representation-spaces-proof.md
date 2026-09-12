---
rg: 2
id: camouflage-prescribes-representation-spaces-proof
kind: route
title: Identify the finite-dimensional representation spaces of stable camouflage groups
target: camouflage-prescribes-representation-spaces
requires:
  - mf-camouflage-surgery
  - mf-camouflage-surgery-preserves-matricial-stability
---

Every map from the full-radical seed `B` to a compact group is trivial: if
such a map had nontrivial image,
Peter--Weyl point separation would produce a nontrivial finite-dimensional
unitary representation of `B`.  Hence `(C1)` applies to `U(n)` and gives the
bijection `(CRS1)`.

Precomposition with `pi_Q` is continuous in the pointwise topology.  Its
inverse is precomposition with the section `s`, hence is continuous as well.
This proves the homeomorphism.  Both maps are defined by composition of
representations with fixed group homomorphisms, so they commute literally
with conjugation, direct sum, tensor product and restriction to invariant
subspaces.  The representation-semiring and irreducible conclusions follow.

If `Q` is stable, `mf-camouflage-surgery-preserves-matricial-stability` says
that `C_d(Q)` is stable.  Its correcting homomorphisms lie in `(CRS1)`, so
every asymptotic model approaches the prescribed representation spaces.

A representation of `F_r` is an arbitrary `r`-tuple of unitaries and a
representation of `Z` is determined by the image of one generator, proving
`(CRS2)--(CRS3)`.  The finite-dimensional irreducibles of `Z` are its
one-dimensional characters.  Finally `(CRS4)` is the camouflage radical
formula with the MF quotient `Z`, and amalgam normal form gives `d!=1`.
