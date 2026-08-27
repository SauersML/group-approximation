---
rg: 2
id: leavitt-first-offdiagonal-packet-breaks-locally-finite-amalgam
kind: claim
title: The first s0/t0 root packet already breaks the locally finite vertices of the modular amalgam
artifacts:
  - research/leavitt-first-offdiagonal-packet-prefix-shift-proof.md
distinct_from:
  leavitt-two-compressor-core-is-lef-and-marked-operator-mf: that proves LEF for the diagonal core by writing it as an amalgam of two locally finite groups; this shows exactly why the same proof does not survive the first off-diagonal coefficient packet.
  leavitt-first-mixed-amenable-face-relator: that finds a shortest kernel word when the degree-zero and upper-parabolic faces are freely amalgamated; this works inside the two-compressor coordinates and exhibits an infinite-order prefix shift in one proposed enlarged vertex.
  leavitt-cylinder-swaps-generate-thompson-in-el: that generates all of Thompson V from the full elementary prefix group; this isolates one cylinder swap and makes no Thompson-V, non-LEF, or MF-radical conclusion about the enlarged core.
---

Let `B_EL=<Lambda,tau_0,tau_1>` be the diagonal two-compressor core, and
fix two distinct coordinates `i,j` in its original rank-five block.  Adjoin
the smallest same-root inverse-prefix packet

```text
u=x_ij(s_0),                 v=x_ij(t_0),
B_EL^(1)=<B_EL,u,v>.
```

Already the subgroup `<Lambda,u,v>` is not locally finite.  More precisely,
it contains an explicit infinite-order prefix substitution `a` satisfying

```text
(i,x)   -> (i,0x),
(j,0x)  -> (j,x),
(j,1x)  -> (i,1x).                                  (FOP1)
```

In particular `a^n(i,x)=(i,0^n x)`, so `a` has infinite order.

Thus the finite-amalgam proof for the diagonal core does not extend by
replacing its lamp group `K` with `<K,u,v>`.  Its load-bearing step was that
both vertex groups `K semidirect C_2` and `K semidirect C_3` are locally
finite, permitting all retained syllables to be placed in finite vertex
subgroups.  Any corresponding enlarged vertex contains `a`, and no finite
subgroup can contain it.

This is a fence on that construction only.  It neither proves that
`B_EL^(1)` is non-LEF nor decides whether its marked diagonal root is visible
in some norm-corona model.  A different normal form or approximation could
still exist.

DERIVATION
leavitt-first-offdiagonal-packet-prefix-shift-proof
