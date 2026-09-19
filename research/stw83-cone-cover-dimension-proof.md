---
rg: 2
id: stw83-cone-cover-dimension-proof
kind: route
title: Convert commuting order-zero cutters into a two-coloured cover of the disk
target: stw83-commuting-cone-two-colour-firewall
requires:
  - stw83-plateau-buffer-recolouring-hinge
---

## The cone has a three-colour floor

The map

```text
Cone(T) -> closed unit disk,             [(r,z)] |-> rz
```

is a homeomorphism.  Suppose that two-label scalar cutters existed for
every positive mesh.  For each cutter put

```text
U_(i,j)=coz(g_(i,j)).
```

The norm bound on the sum says that the `U_(i,j)` cover the disk.
For fixed `i`, orthogonality of the positive functions makes the
sets `U_(i,j)` pairwise disjoint.  The cover therefore has
multiplicity at most two, and its mesh is less than `epsilon`.

Let `V` be any finite open cover of the disk and let `lambda>0` be
a Lebesgue number.  A two-label cutter of mesh smaller than `lambda`
would give an open refinement of `V` of multiplicity at most two.
If cutters existed at every scale, the covering dimension of the disk
would consequently be at most one.  This contradicts

```text
dim(closed unit disk)=2.
```

Hence some `epsilon_0>0` has the asserted property.

This is exactly the support condition seen by a scalar
functional-calculus construction.  An order-zero map from a
finite-dimensional algebra to an abelian algebra vanishes on every
noncommutative matrix summand.  Its nonzero coordinate images are
pairwise orthogonal positive functions.  Thus two outgoing labels give
the two disjoint families above.  Contractive reconstruction of the
unit gives the displayed lower bound on their sum, while locality of
the evaluation blocks in the joint character `(r,z)` gives the mesh
condition.  Equivalently, a universal two-colour approximation of this
commuting joint functional calculus would make
`dim_nuc(C(Cone(T)))<=1`, whereas the commutative computation gives
`dim_nuc(C(Cone(T)))=2`.

In the Toeplitz-module model, a continuous cutoff and the coefficient
phase have precisely this cone geometry: at cutoff zero the phase is
invisible, and at positive cutoff the joint coordinate is `rz`.
Therefore a construction which spreads coefficient variation through
the entire transition and uses only commuting scalar cutters meets the
hypotheses above.  Notice the scope: the proof does not apply when the
coefficient-varying compact part has already vanished before the
transition.  That is why the finite-set-adaptive scalar-buffer route
remains open.

## The block-diagonal endpoint

For completeness, take `D=M_r(C(T))`, a nontrivial constant
projection `p`, and `q=1-p`.  Assume two-colour approximations of
`id_D` have first outgoing range in `pDp` and second outgoing map
`eta` commuting with `p`.  Restrict the incoming maps to `qDq`
and compress the outgoing maps by `q`.  The first colour disappears.
Because `q` commutes with the range of `eta`, the map

```text
x |-> q eta(x) q
```

is still cpc order zero.  The compressed approximations would therefore
give nuclear dimension zero for `qDq`.  But `q` has positive
constant rank, so

```text
qDq = M_s(C(T))
```

for some `s>=1`, and this algebra has nuclear dimension one.  This is
the claimed contradiction.

The cone argument rules out coupled commuting scalar cutters, not just
independent partitions.  The compression argument rules out the
constant-projection block-diagonal endpoint.  Together they force any
remaining construction to use the noncommuting, stage-dependent buffer
geometry stated in the target, without asserting that such a
construction exists.
