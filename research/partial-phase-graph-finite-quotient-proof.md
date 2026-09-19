---
rg: 2
id: partial-phase-graph-finite-quotient-proof
kind: route
title: Preserve partial graph pinches using Hall covers and one finite phase quotient
target: partial-phase-graph-hnn-is-residually-finite
requires: []
---

We first record the finite-quotient fact needed for the free coordinate.  If
`A<=L` is finitely generated, `K normal A` has finite index, and
`ell_1,...,ell_r` lie outside `A`, then there is a finite quotient
`q_L:L->Q` such that

```text
ker(q_L|_A)<=K,                 q_L(ell_j) notin q_L(A). (PPG3)
```

Indeed Marshall Hall's theorem puts `A` as a free factor of a finite-index
subgroup `H<=L`.  The retraction `H->A->A/K` has finite-index kernel `M` with
`M intersect A=K`; the core of `M` in `L` gives the first condition.  Free
groups are subgroup separable, so for each `ell_j` there is a finite-index
subgroup containing `A` but not `ell_j`.  Intersecting the cores of these
subgroups with the first core gives `(PPG3)`.

Now let `w` be a nontrivial Britton-reduced word in `(PPG2)` containing a
stable letter, and write its intervening base syllables as `(ell_j,p_j)`.
For `nu=0,1`, membership in the associated subgroup is tested by

```text
(ell_j,p_j) in G_nu
 iff ell_j in A and p_j=Theta_nu(ell_j).                (PPG4)
```

For every forbidden pinch with `ell_j in A`, residual finiteness of `P`
gives one finite quotient `q_P:P->F` preserving the nonidentity element
`p_j Theta_nu(ell_j)^(-1)`.  Take one quotient preserving all finitely many
such tests and put

```text
K=ker(q_P Theta_0) intersect ker(q_P Theta_1) normal A. (PPG5)
```

Apply `(PPG3)` to this `K` and to all syllables with `ell_j notin A`.  Both
maps `q_P Theta_nu` then descend to homomorphisms

```text
Theta_bar_nu:q_L(A)->F.
```

Thus `L times P -> Q times F` induces a homomorphism to the HNN extension of
the finite group `Q times F` between the two finite graph subgroups of the
`Theta_bar_nu`.  Every nonmembership test in `(PPG4)` survives, so the image
of `w` is still Britton reduced and nontrivial.  This finite-base HNN is
virtually free and residually finite, and a further finite quotient separates
the image of `w`.

If `w=(ell,p)` is a nontrivial base element, additionally intersect the core
in `(PPG3)` with a finite quotient kernel of `L` avoiding `ell` when needed,
and choose `q_P` avoiding `p` when needed.  The same construction keeps
`(ell,p)` nontrivial.  Hence every nonidentity element of `E` survives in a
finite quotient, proving residual finiteness.
