---
rg: 2
id: full-mf-radical-dynamical-rigidity-proof
kind: route
title: Detect compact and Koopman structure by finite-dimensional unitaries
target: full-mf-radical-dynamical-rigidity
requires:
  - hilbert-hotel-model-full-mf-radical
artifacts:
  - research/full-mf-radical-dynamical-rigidity.md
---

Every countable complex linear group is MF.  Indeed, it is the directed union
of its finitely generated subgroups; Malcev makes each of those residually
finite, residually finite groups are MF, and the local characterization of MF
passes to directed unions.  The image of a representation of the countable
group `G` is countable, so total MF radical kills every finite-dimensional
complex linear representation.  For unitary targets this is also immediate
from the constant matrix corona containing `U(n)`.

The projective unitary group `PU(n)` is a compact linear group via its
adjoint representation, hence an MF group.  Therefore every homomorphism
`G -> PU(n)` is trivial.

If `f : G -> K` has compact Hausdorff target and nontrivial image,
Peter--Weyl point separation supplies a finite-dimensional unitary
representation of `K` which is nontrivial on `f(G)`.  Its composite with
`f` contradicts total MF radical.  This proves the compact conclusion and
triviality of the Bohr compactification.  A proper finite-index subgroup
would give a nontrivial permutation action on its cosets, hence a nontrivial
homomorphism to a finite symmetric group.

Let `G` act ergodically on a probability space.  A nonzero
finite-dimensional invariant subspace of `L^2_0` would give a
finite-dimensional unitary representation.  Total MF radical makes this
representation trivial, so every vector in the subspace would be invariant.
Ergodicity leaves no invariant vectors in `L^2_0`, a contradiction.  This is
the standard Koopman criterion for weak mixing.

If `G` has property `(T)`, the Koopman representation on `L^2_0` has no
invariant vector and therefore has spectral gap.  Spectral gap implies strong
ergodicity.  The Hilbert-hotel group has property `(T)` and full MF radical,
so the final specialization follows.
