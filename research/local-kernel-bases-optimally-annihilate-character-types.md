---
rg: 2
id: local-kernel-bases-optimally-annihilate-character-types
kind: claim
title: A basis of the local kernel optimally annihilates all excluded character types
root: true
artifacts:
  - research/local-kernel-bases-optimally-annihilate-character-types-proof.md
distinct_from:
  forbidden-character-kernel-quotient-compiler: that proves nonhyperlinearity once every forbidden type is detected by the perfect-model kernel; this gives the smallest local relation package implementing that quotient.
  locally-affine-support-bcs-is-exactly-the-lcs-boundary: that identifies the surviving affine character packet; this computes the optimal number of group relators defining it.
  finite-phase-scalar-groupification-iff-coset-subgroup: that characterizes scalar profiles in one central-character sector; this gives the exact annihilator presentation and its minimality for a specified subgroup kernel.
---

Let `H` be a finite abelian group, let `J in H` be an involution, and let
`K<=H` satisfy

```text
K intersect <J>={1}.                                   (LKB1)
```

For `W subseteq K`, write `L=<W>`.  Quotienting by the relations `w=1`,
`w in W`, preserves exactly the characters trivial on `L`; in the marked
sector it preserves

```text
X_-(L)={chi in widehat(H): chi(J)=-1, chi|L=1}.        (LKB2)
```

Therefore the relations indexed by `W` produce exactly the target marked
packet `X_-(K)` if and only if

```text
<W>=K.                                                  (LKB3)
```

In particular, the smallest number of local relations defining the packet
is the minimal number of generators `d(K)`.  When `H` is elementary abelian,

```text
d(K)=dim_(F_2) K.                                      (LKB4)
```

Applied to a perfect contextual representation `theta`, take

```text
K_c=ker(theta) intersect H_c.                          (LKB5)
```

If every forbidden marked character is nontrivial on `K_c`, then adjoining
relations for one basis of `K_c` annihilates every forbidden character in
that context simultaneously.  The number of added relations is at most the
number of context generators, independent of the number of forbidden
assignments.

For finitely many contexts, take the normal closure of the union of these
local bases.  It remains inside `ker(theta)`, so the perfect model descends,
and `forbidden-character-kernel-quotient-compiler` applies.  This gives a
linear-size quotient presentation whenever the locally affine support
condition holds.
