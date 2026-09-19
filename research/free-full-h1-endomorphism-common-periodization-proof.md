---
rg: 2
id: free-full-h1-endomorphism-common-periodization-proof
kind: route
title: Promote every full-H1 branch to an automorphism of one marked pro-p quotient
target: full-h1-rank-free-endomorphism-families-periodize
requires: []
artifacts:
  - research/artifacts/free-full-h1-endomorphism-common-periodization-proof.md
---

Choose a prime `p` dividing none of the nonzero determinants of the maps
induced by `phi_1,...,phi_r` on `H_1(F_n;Z)`.  Embed `F_n` densely in its free
pro-`p` completion `P`; the embedding is injective because a free group is
residually a finite `p`-group.  Each `phi_i` extends uniquely to a continuous
endomorphism `hat phi_i:P->P`.

The Frattini quotient of `P` is

```text
P/Phi(P) = H_1(F_n;F_p).
```

Our choice of `p` makes every `hat phi_i` invertible on this quotient.  The
pro-`p` Burnside basis argument then makes `hat phi_i` surjective: the closure
of its image together with `Phi(P)` is all of `P`, and a proper closed subgroup
is contained in a maximal open subgroup, which contains `Phi(P)`.  A
topologically finitely generated profinite group is Hopfian, so each
`hat phi_i` is an automorphism.

Because `y!=1` in `P`, choose an open normal subgroup `U` not containing `y`.
There are only finitely many open subgroups of `P` of any bounded index: a
`d`-generated profinite group has only finitely many continuous actions on a
fixed finite set.  Intersect every open subgroup of index at most `[P:U]` and
call the result `C`.  Then `C` is open, characteristic, contained in `U`, and
normal.  Thus the finite `p`-group `Q=P/C` detects `y`, and all the
`hat phi_i` descend simultaneously to automorphisms `bar phi_i` of `Q`.

Finally, the dense map `F_n->P` surjects onto the finite quotient `Q`.  Sending
the stable letter `t_i` to `bar phi_i` and the base to `Q` respects every
relation `t_i g t_i^(-1)=phi_i(g)`, and gives the asserted finite marked
quotient

```text
Q rtimes <bar phi_1,...,bar phi_r>.
```

The artifact supplies proofs of the residual-`p`, Burnside-basis, Hopficity,
and bounded-index steps used above, so the conclusion does not assume a
simultaneous periodic-point theorem.
