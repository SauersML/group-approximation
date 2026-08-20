---
rg: 2
id: free-factor-phase-graph-finite-quotient-proof
kind: route
title: Extend one synchronized finite support quotient across both free complements
target: free-factor-phase-graph-hnn-is-residually-finite
requires: []
---

We use the following elementary free-factor quotient lemma.  Suppose

```text
L=A * C,
```

`N normal A` has finite index, `ell_1,...,ell_r` lie outside `A`, and
`u_1,...,u_s` are nonidentity elements of `L`.  After replacing `N` by a
smaller finite-index normal subgroup if necessary, there is a finite quotient
`q:L->Q` such that

```text
ker(q|_A)=N,                    q(ell_j) notin q(A),
q(u_k)!=1.                                               (FFG2)
```

To see this, write the finitely many `ell_j` in reduced `A*C` normal form and
refine `N` so every nontrivial `A` syllable needed to keep those forms reduced
survives.  The quotient map

```text
A*C -> (A/N)*C
```

then keeps each image outside the finite factor `A/N`; refine `N` in the same
way so every `u_k` also has nontrivial image.  The free product on the right is
residually finite.  Since `A/N` is finite, one finite quotient is injective on
`A/N`, keeps every chosen image outside it, and preserves every `u_k`: separate
the finitely many relevant elements and products with `A/N`, then intersect
the kernels.  The composite is `(FFG2)`.

Now take a Britton-reduced word in the claimed HNN containing a stable letter.
For each intervening base syllable `(ell_0,ell_1,p)`, nonmembership in `G_0`
or `G_1` is certified either by a faithful coordinate outside `j_nu(A)`, by a
nontrivial opposite coordinate, or by a nonidentity phase difference in `P`.
Choose one finite quotient `q_P:P->F` preserving all phase certificates.  In
the abstract support group choose a finite-index normal subgroup

```text
N <= ker(q_P Theta_0) intersect ker(q_P Theta_1)        (FFG3)
```

small enough to preserve all nontrivial support syllables needed in the two
applications of `(FFG2)`.  Apply that lemma to
`L_0=j_0(A)*C_0` and `L_1=j_1(A)*C_1`, using the same quotient `A/N` at both
ends and including every nontrivial opposite-coordinate pinch certificate
among the `u_k`.  Both phase maps descend, both associated graph subgroups
become copies of `A/N`, and every forbidden pinch survives in the finite base

```text
Q_0 times Q_1 times F.
```

The word therefore remains Britton reduced in an HNN of a finite group along
finite subgroups.  That group is virtually free and residually finite, so a
further finite quotient separates the word.  A nontrivial base word is handled
by refining `N`, `q_P`, or the free-complement quotients to preserve one
nonidentity coordinate.  Hence the original HNN is residually finite.
