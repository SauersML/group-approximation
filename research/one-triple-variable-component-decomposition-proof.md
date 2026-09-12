---
rg: 2
id: one-triple-variable-component-decomposition-proof
kind: route
title: Decompose one triple-used variable into graph components and one-port factors
target: one-triple-variable-lcs-has-no-perfect-model-gap
requires:
  - degree-two-operator-ports-are-boundary-edges
  - magic-square-one-port-is-a-universal-phase-absorber
---

# Decompose one triple-used variable into graph components and one-port factors

## 1. The degree-two skeleton

Let `L` have central involution `J`, one variable `z` occurring in three
distinct equations, and every other variable occurring at most twice.
Delete `z` from its three equations.  Make a vertex for every equation and
an edge for every remaining variable of occurrence two.  Variables of
occurrence one are boundary half-edges.  Let `G_1,\ldots,G_m` be the
connected components of the ordinary edge skeleton.

For component `G_k` let `t_k` be the number of deleted `z` occurrences in
that component.  Then

$$
t_k\in\{0,1,2,3\},
\qquad
\sum_k t_k=3.                                         \tag{1}
$$

Apart from zero entries, the partition of three in (1) is `3`, `2+1`, or
`1+1+1`.

A component containing an occurrence-one half-edge is harmless.  For either
scalar choice `z=\pm1`, its binary incidence system is solvable: ordinary
edge columns span the even-parity vectors of a connected component, and a
weight-one column toggles parity.  Choosing scalar solutions in the two
`z` sectors and taking their spectral direct sum extends an arbitrary
involution `z`.  We henceforth call such a component **free**.

Components with `t_k=0` and no half-edge are ordinary closed
graph-incidence systems.  If `J\neq1` in the full solution group, none of
these component presentations can force `J=1`, since the same relator proof
would hold in the full group.  By Paddock--Russo--Silverthorne--Slofstra,
[Theorem 4.1 and Corollary
4.7](https://doi.org/10.5802/alco.292), each therefore has a
finite-dimensional representation with `J\mapsto-I`.  They can be tensored
onto the construction below and will be suppressed.

## 2. One-port component lemma

Consider a connected component `G` with no half-edge and exactly one
`z` occurrence, at a context `v`.  Let

$$
p=\sum_{u\in V(G)}b(u)\pmod2.                        \tag{2}
$$

There is a sharp dichotomy.

### Planar case: the port is pinned

Embed `G` in a disk and draw the `z` half-edge from `v` to the boundary.
The planar picture used in the proof of Arkhipov's theorem has one
2-cell for each vertex relation.  Every ordinary edge label appears twice
and cancels using the incident-edge commutations; the only boundary label is
`z`.  The vertex signs contribute `J^p`.  Hence the partial solution group
has the exact relation

$$
\boxed{z=J^p.}                                        \tag{3}
$$

This is the one-boundary version of the picture construction in Section 4
of the cited paper.  On the `J=-1` sector the port is one fixed scalar sign,
and the remaining scalar incidence equations have even parity, hence a
classical solution.

### Nonplanar case: the port is absorbed

Let `Z` be any involution on a finite-dimensional space `H` and let
`Q_\pm=(I\pm Z)/2`.  If `z` is replaced by the scalar sign `s`, the
remaining system is the graph-incidence system on `G` with one vertex sign
toggled according to `s`.  The two choices of `s` have opposite total
parity.  The even profile has a scalar solution; the odd profile has a
finite-dimensional operator solution because `G` is nonplanar, by
Arkhipov's theorem.  Amplify the two models to a common finite dimension
`d` and set

$$
X_e=Q_+\otimes X_e^+ + Q_-\otimes X_e^-.
$$

This extends `Z` on `H\otimes\mathbb C^d`.  Thus a nonplanar one-port
component accepts every finite-dimensional source involution.

Together with the free case, every one-port component either pins `z` to
one scalar character of `\langle J,z\rangle` or is a finite-dimensional
absorber.

## 3. Components with two or three occurrences

If `t_k=2`, the two uses of `z` are exactly the two endpoints of an ordinary
graph edge.  The component, including `z`, is therefore a closed
graph-incidence system.  Whenever its `J` is nontrivial, Arkhipov's theorem
supplies a finite-dimensional representation with `J=-I`.

If `t_k=3`, the component has a scalar solution for every prescribed vertex
colouring after a suitable scalar choice of `z`.  Indeed, the ordinary
incidence columns span exactly the even-parity vectors, whereas the
`z` column has weight three and hence odd parity.  Choose the bit assigned
to `z` so that the adjusted right-hand side is even, then solve with the
ordinary edges.  Thus a `t_k=3` component already has a one-dimensional
`J=-1` representation.

## 4. Assemble the three possible distributions

Assume `J\neq1` in the full solution group.  Since `J` is central of order
two, it has a representation with `J=-I`.  We construct a
finite-dimensional one.

### Pattern `3`

The unique marked component has a scalar solution by Section 3.  Tensor it
with the finite-dimensional `t_k=0` component representations from
Section 1.

### Pattern `2+1`

The two-occurrence component is graph incidence, so choose a
finite-dimensional representation `\rho` with `\rho(J)=-I`.

If the one-port component is free or nonplanar, its absorber construction
extends the involution `\rho(z)` after a finite amplification.

If the one-port component is planar, (3) forces
`z=J^p` in the full group.  Hence the restriction of the assumed
`J=-I` representation to the two-occurrence component factors through the
scalar quotient `z=(-1)^pI` and still has `J=-I`.  Substituting this scalar
deletes the `z` edge and toggles its two endpoint signs, leaving another
closed graph-incidence system.  Corollary 4.7 gives a finite-dimensional
`J=-I` representation of that quotient.  The planar one-port component has
a scalar solution with the same `z`, so the two representations agree.

### Pattern `1+1+1`

Every marked component is a pin or an absorber.  If two planar pins required
different values of `z` on the `J=-1` sector, their exact relations (3)
would imply `J=1` in the full group, contrary to the assumption.  Choose
the common pinned scalar sign; if there is no pin, choose either sign.

A planar pinned component has a scalar solution for that sign.  A free
component has a scalar solution for either sign.  A nonplanar component has
a finite-dimensional solution for either sign: its fixed-sign profile is
either even and classical or odd and covered by Arkhipov.  Tensor the
component representations.  Their copies of `J` and `z` are the same
scalars, so this is a representation of the full presentation.

In every case `J` survives in finite dimension.  The converse is immediate,
which proves the claim.

## 5. The diagonal-pushout viewpoint

Splitting the three occurrences into boundary involutions `z_1,z_2,z_3`
turns the skeleton into an open degree-two incidence group `\Pi`.  Restoring
the original variable is the diagonal quotient

$$
\Gamma_L
\cong
\Pi/\langle\!\langle z_1z_2,\ z_2z_3\rangle\!\rangle.        \tag{4}
$$

Equivalently it is the pushout of `\Pi\leftarrow
(C_2*C_2*C_2)\to C_2`, where the right map folds all three free factors to
one involution.  This is not an amalgamated free product over an injected
finite subgroup: the fold map has a nontrivial kernel.  Sections 1--4 show
that one such diagonal fold is nevertheless marked-`J` tame.

The result is exact, not quantitative.  No uniform Hilbert--Schmidt
stability constant for the diagonal quotient is asserted.
