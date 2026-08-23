---
rg: 2
id: dyadic-ob-inertia-arrows-have-exact-induction-functors
kind: claim
title: The fixed-to-OB and OB-to-OB inertia arrows are exact induction functors
distinct_from:
  adjacent-clifford-orbit-transition-graph: that counts the sharp source capacities of all orbit arrows but does not construct the projective inertia functors or compute their target dimensions.
  adjacent-clifford-flow-has-one-third-rank-deficit: that bounds all adjacent matches using the one-third target slots and states induction labelwise; this gives the explicit quotient homomorphism, constructs the functor on arbitrary modules, and computes the two dimension factors separately.
  fixed-clifford-sectors-have-zero-adjacent-opposite-overlap: that excludes the fixed-to-fixed arrow and identifies the required OB target orbit; this constructs every fixed-to-OB arrow functorially.
  dyadic-invariant-cocycle-has-a-stable-heisenberg-sign: that computes a stable alternating sign in the full-inertia multiplier; this proves that the sign and the OB inertia multiplier are compatible along the actual edge functor.
---

Let `B_a^+` be the upper-Iwahori image in
`G_a=SL_2(Z/2^a)`, and let `B_(a+1)^-` be the opposite-Iwahori image in
`G_(a+1)`.  There is a natural surjection

```text
r_a:B_(a+1)^- -> B_a^+                                  (DOI1)
```

obtained by representing an opposite element as `sigma(gamma)` and sending
it to the upper reduction of `gamma` one level lower.

For a `G_a`-representation `V`, let `W_1(V)` be the sum of the newest-layer
character spaces `(alpha,beta,gamma)` with `beta=1`.  It is
`B_a^+`-invariant.  The exact additive functor

```text
F_a(V)=Ind_(B_(a+1)^-)^(G_(a+1)) (W_1(V) o r_a)          (DOI2)
```

has newest-layer orbit `O_B`.  On the two source sectors relevant to the
recurrent transition graph it has dimensions

```text
V over O_F:  dim W_1(V)=dim V,       dim F_a(V)=3 dim V,
V over O_B:  dim W_1(V)=2 dim V/3,   dim F_a(V)=2 dim V. (DOI3)
```

Transposing the two root charts gives the reverse-orientation functor with
`beta=1` replaced by `gamma=1`, and the same two dimension formulas.

Thus both `O_F -> O_B` and `O_B -> O_B` are realized by honest
representation functors at their sharp source capacities.  In particular
their projective inertia multipliers and central characters are compatible;
there is no extra Schur-multiplier, parity, or categorical divisibility
obstruction that deletes either arrow.

The price is physical-dimension inflation by `3` and `2`, respectively.
In both cases the target is three times the *matched edge module*: for an
`O_B` source that module was already only `2/3` of the source.  Direct sums
of fixed and recurrent sources do not change this index-three target ratio.
Thus all lower-to-higher arrows together occupy at most one third of their
targets, and the reverse orientation has the same constraint.  This is the
target-slot charge in `adjacent-clifford-flow-has-one-third-rank-deficit`,
not a projective central-character incompatibility.

Consequently `(DOI2)` is not by itself a Folner packet.  The complete
scalar orbit-capacity window can fill the other slots using the reverse
adjacent orientation and a diagonal cell, but `(DOI2)` neither constructs
nor obstructs the required simultaneous decomposition of one projective
inertia label.  That three-way compatibility is the remaining information
missing from the individual functors.
