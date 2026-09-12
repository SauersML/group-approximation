---
rg: 2
id: unitary-group-embedding-recovers-the-corner-decomposition
kind: claim
title: An injective scalar-preserving unitary group embedding recovers the one-to-two corner decomposition
refuted_by: unitary-embedding-does-not-preserve-corner-orthogonality
---

REFUTED.  The proposed step starts in a properly infinite operator algebra,
where an isometry carries a genuine one-to-two range decomposition, embeds
that algebra's abstract unitary group into finite matrices, and reads the
decomposition back off the images of the reflections `r_p=I-2p`.  The
embedding was allowed to be arbitrary subject to injectivity, unitality and
preservation of the scalar unitaries.

Those hypotheses do not force the induced projection map to respect the
projection lattice.  `unitary-embedding-does-not-preserve-corner-orthogonality`
gives an exact 27-dimensional counterexample: `u -> u tensor u tensor bar(u)`
on `U(3)` is injective, multiplicative and fixes every scalar unitary, yet
sends two orthogonal rank-one projections to commuting rank-13 projections
whose product has rank 6, and it fails additivity with an error of operator
norm 2.  So the recovered "corner" need be neither orthogonal nor additive,
and no completeness or inverse row can be read off it.
