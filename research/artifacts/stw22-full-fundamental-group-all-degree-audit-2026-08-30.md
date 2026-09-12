# Audit: all-degree fillings for full-fundamental-group fibres

## Status

PASS for one fixed separable-predual `II_1` factor whose fundamental group
is all of `R_+^*`.  FAIL as an unconditional argument for arbitrary fixed
factors beyond `S^2`.

## Corner scaling

The full-fundamental-group hypothesis is used only to identify every
normalized nonzero corner with the same `N`.  The isomorphisms preserve the
unique normalized traces.  If a corner has trace below
`(min(epsilon,1)/4)^2`, its entire ambient `2`-diameter is already below
`epsilon/2`.  On all other corners, normalized and ambient metrics differ
by `sqrt(t)`, bounded below by `min(epsilon,1)/4`.  Transporting one pointed
Jekel contraction therefore gives a positive modulus uniform over all
corners.  No continuous choice of corner isomorphisms is used or needed.

## Michael hypotheses

Conjugator fibres are cosets of one complement-corner unitary group.  They
are closed and lower semicontinuous by the quantitative polar correction.
The transported contractions make the whole family globally connected and
uniformly equi-locally connected in every finite degree.  Gutev's controlled
theorem with `n=k-1` applies to `S^k`; its uncontrolled counterpart gives
global lifts.  The selected sphere lift is contracted by the pointed
contraction in the fixed ambient `N`, so the small filling retains an exact
unitary lift over the ball.

## Weights and limits

Multicopy frames are encoded in `N` itself, not in `M_m(N)`.  The high-low
cut therefore introduces no `m`-dependence in the Stiefel modulus.  The
relative low-band construction is dimension-free once every fixed-corner
Stiefel sphere has a unitary-lifted filling.  At each finite stage the
remaining complement is explicitly trivialized; no infinite product of
unitaries is taken.  Only the orthogonal weighted sums converge.  Uniform
operator bounds put the limits in `N`, and `L^1` convergence of products
preserves all exact algebraic identities and the boundary.

## General-factor firewall

A pointed contraction of `U(N)` does not preserve an arbitrary corner.
Separate contractions of `U(rNr)` have no known common local modulus as
`r` varies.  To lift `S^3`, controlled Michael selection needs precisely a
uniform equi-`LC^2` modulus for these corner stabilizers.  The unconditional
diffuse theorem supplies only the preceding loop degree.  Hence the
fixed-factor `S^2` theorem cannot simply be iterated for arbitrary `N`.
This audit makes no negative claim about the truth of higher-degree
uniformity; it rules out only the unsupported pointed-Jekel bootstrap.

## Trace consequence

For finite-dimensional compact Hausdorff `K`, degree `d-1` Michael
selection is available in the common complete space `L^2(N)^m`; take the
minimum of the finitely many degree-wise moduli to obtain the one
equi-`LC^(d-1)` modulus used there.  The
trivial Hilbert module is countably generated since `L^2(N)` is separable,
even when `K` is not metrizable.  The existing spectral-cut replication
argument and exact gap criterion then force every trace to be canonical.
