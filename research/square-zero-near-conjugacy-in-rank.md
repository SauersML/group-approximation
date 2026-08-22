---
rg: 2
id: square-zero-near-conjugacy-in-rank
kind: claim
title: Close square-zero maps of the same rank are conjugate by a rank-small basis change
distinct_from:
  atlas-q14-rank-centralizer-projection: that projects one map linearly into a centralizer but can lose square-zero type; this starts with two exact square-zero maps of the same type and controls the conjugating basis change.
---

ESTABLISHED.  Let `A,B in M_n(k)` satisfy

```text
A^2=B^2=0,       rank A=rank B,
e=rank(A-B).                                           (SZC1)
```

Then there is `S in GL_n(k)` such that

```text
S A S^(-1)=B,       rank(S-1)<=8e.                    (SZC2)
```

Only the existence of a universal constant is used downstream.

### Proof

Put

```text
K=ker(A-B) intersect A^(-1)(ker(A-B)).                 (SZC3)
```

Then `codim K<=2e`.  On `K`, the two maps agree.  Moreover `K` is invariant
under both: if `v in K`, then `Av=Bv` lies in `ker(A-B)`, and its image under
either square-zero map is zero.

Use Jordan chains of length at most two.  From a common invariant subspace of
codimension `c`, delete every common chain which either lacks a predecessor
inside the subspace or is hit by a predecessor outside it, for either of the
two ambient maps.  Row reduction in the image/kernel flag

```text
im A <= ker A,       im B <= ker B                     (SZC4)
```

shows that at most `c` terminal directions and their at most one chain
predecessor are deleted for each map.  Thus `K` contains a common submodule
`H` which is a direct summand for both `A` and `B`, on which they agree, and

```text
codim H<=4c<=8e.                                      (SZC5)
```

The complements have the same numbers of length-two and length-one Jordan
blocks: the full modules have the same dimension and rank, and the common
summand has one fixed block type.  Choose a module isomorphism between the
two complements and take it to be the identity on `H`.  The resulting `S`
intertwines `A` and `B`, while `S-1` vanishes on `H`; `(SZC2)` follows.
