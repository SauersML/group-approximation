---
rg: 2
id: adaptive-prefix-atom-rank-return-fence-proof
kind: route
title: Separate partial orbit growth, close-projection rank rigidity and genuine finite actor actions
target: adaptive-prefix-atom-rank-return-does-not-close-opnorm-row
requires:
  - exact-lamp-lifts-admit-moving-pair-kernel-jumps
  - binary-leavitt-finite-actor-minimal-atom-dichotomy
  - binary-leavitt-root-doubling-k0-retains-xor-overlap
---

For `(APR1)`, use the standard coordinate basis and let `W_(L,j)` be the
transposition of `delta_(j-1)` and `delta_j`.  Conjugating its source
rank-one projection gives its target rank-one projection exactly.  Since the
coordinate lines are mutually orthogonal, no source projection returns
inside the displayed path.  Taking `L` to grow with the ambient dimension
shows that finite rank gives no uniform return length.

For `(APR2)`, write unit vectors `e` and
`f=cos(theta)e+sin(theta)e_perp`.  On their two-dimensional span the
difference of the two rank-one projections has eigenvalues
`+sin(theta),-sin(theta)`, so its operator norm is `sin(theta)`.  Thus the
strict-one projection lemma proves equality of ranks, not equality of
projections or equality of their multiplicity reservoirs.

An action on atoms is a map to a symmetric group only when every generator
sends every member of one finite set back into that same set and the actor
relators hold on the induced permutations.  The path `(APR1)` has no such
terminal edge.  Adding its next image preserves exact covariance but moves
the missing terminal edge one step farther out.  Therefore a no-finite-action
theorem has no input until a uniform invariant closure has separately been
proved.

The two required citations show that neither routine repair supplies that
closure.  Exact commuting lifts are unconstrained at a coordinate-dependent
frontier, as witnessed by an operator-norm-two moving kernel jump.  Freezing
a finite invariant packet instead admits an exact finite dual-permutation
model with arbitrary multiplicity fibers and no Leavitt return.  The claimed
scope fence follows.
