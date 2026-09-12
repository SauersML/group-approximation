---
rg: 2
title: STW LXXXII zero-dimensional central-support recolouring audit (2026-08-30)
kind: artifact
---

# Positive replacement mechanism

The support-local coupled-cover theorem leaves open whether one can replace
an outgoing family rather than preserve its global support graph.  A common
zero-dimensional central support algebra supplies an asymptotically exact
mechanism whose cut pieces remain exactly order zero.

At each point of its spectrum, list the outgoing supports which are nonzero.
If at most `m` are active, assign them injectively to `m` labels.  The
assignment need not be globally consistent.  For a prescribed error, a
finite clopen partition makes every support omitted from a block uniformly
small there.  The label assignment may then vary independently across the
clopen blocks.  The corresponding characteristic projections commute with
all outgoing maps, so cutting preserves order zero exactly; equal labels are
orthogonal block by block.

This proves that the asymptotic number of central coupled labels is exactly
the maximum pointwise support multiplicity.  No cone-projectivity repair is
needed in this regime, although the result feeds directly into the general
support-local theorem.

For a finite-dimensional algebra of central atoms the conclusion sharpens:
the cover is exact, and atom depth is the minimum even among covers by
arbitrary multiplier cutters.  Compressing to one central atom turns every
active support into a scalar multiple of the corner unit; a state on that
corner and fixed-label orthogonality then give the sharp lower bound.  The
general zero-dimensional result is deliberately approximate.  Exact
pointwise depth can fail at accumulating support boundaries.  For example,
in `C([-1,1])` the functions

```text
h_-(t)=max(-t,0),       h_+(t)=max(t,0)
```

have cozero multiplicity one.  An exact one-label cover would force its two
continuous cutters to be one on the negative and positive open half-lines,
respectively; continuity makes both equal one at zero, contradicting their
orthogonality.  This does not conflict with the approximate theorem, which
may discard a shrinking low-amplitude neighbourhood of zero.

# Odd-cycle elimination

Three supports over three central atoms can overlap in the pattern

```text
1--2 at a,       2--3 at b,       3--1 at c.
```

Their global overlap graph is a triangle, so preserving each outgoing map
requires three colours.  No atom sees more than two supports.  Reversing the
two labels as one moves between atoms and splitting each map by the three
central projections gives two global order-zero colours.  This is the
smallest explicit instance in which replacement eliminates the odd-cycle
obstruction rather than merely imposing bipartiteness on the original
family.

# Relation to extension geometry

For a reduced separable stable essential extension, the theorem gives a new
exact target for an optimal gluing construction: arrange the endpoint
outgoing supports in a common zero-dimensional abelian multiplier algebra
which centralizes all outgoing ranges, with pointwise multiplicity at most
`max(p,q)+1`.  If this is achieved at every approximation scale, the maximum
formula follows by direct recolouring.

This is an outgoing-family selection theorem, not a claim that arbitrary
extensions possess the required central support algebra.  Central or
zero-dimensional support geometry is not automatic in an essential
extension, and the earlier `M_2` triangle shows why trace capacity cannot
replace it.  The theorem is also distinct from the known subhomogeneous and
quasidiagonal extension classes: its hypothesis is local to the chosen
nuclear approximations, and its conclusion follows by blockwise replacement
rather than by a projectional quasicentral approximate unit or a dimension
formula for primitive spectra.
