# Audit: fixed-factor two-sphere fillings

## What is uniform

The loop modulus for unitary groups of all diffuse corners is converted
from normalized to ambient trace in `(S2-1)`; the case of a tiny corner is
handled by its diameter.  Thus the conjugator fibres have a single
equi-`LC^1` modulus independent of their corner traces.  Gutev's controlled
selection consequently gives a small `S^2` unitary lift with control
independent of the source projection.

The final contraction modulus is different.  Pointing a fixed Jekel
contraction and applying the tube lemma gives `lambda_N(epsilon)`, which may
depend on `N`.  The claim fixes `N` and never promotes this number to a
factor-uniform constant.

## Lift and topology checks

The conjugator fibre of a frame is one corner unitary group, not a product:
it fixes the final projection pointwise and is arbitrary on its complement.
It is closed, lower semicontinuous in the frame parameter, simply connected,
and uniformly equi-`LC^1`.  These are exactly the hypotheses of Michael's
degree-one selection theorem on `S^2`.  The selected lift contracts through
unitaries, so projection to the Stiefel space gives both a filling and a
unitary trivialization of its complement.

For relative low bands, only an uncontrolled `S^2` lift in the current fixed
corner is required.  The same selection theorem gives it, and Jekel fills
it over `B^3`.  Updating the complement by the filled unitary is exact; no
sequence of unitary trivializations is asserted to converge.

## Weighted limit and selection consequence

The band sums have the same orthogonal-tail identity and uniform operator
bound as in the loop theorem.  Their `L^2` limits lie in `N`; sources and
cross products pass to `L^1`, preserving exact range orthogonality.  The
high and low costs are `epsilon_0/3` and `epsilon_0/6`.

For the trivial bundle, all values live in the fixed complete space
`L^2(N)^m`.  Lower semicontinuity is the established correction lemma, and
the new `S^2` theorem supplies the final equi-`LC^2` hypothesis for
degree-two Michael selection over bases of dimension at most three.

## Remaining arbitrary-factor hinge

This does not prove a modulus uniform over all separable `II_1` factors.
The exact missing estimate is a factor-uniform pointed local contraction
modulus for `U(N)` on small `S^2` maps (equivalently, a replacement such as
a two-dimensional continuous small-trace spectral-capture theorem).  Jekel
proves contractibility factor by factor but does not state this quantitative
uniformity; Farah--Vaccaro likewise explicitly identify equi-local
connectivity of the selection fibres as the higher-dimensional obstacle.
The tempting multiplicity-three union of local hard carriers does not supply
that replacement: `stw22-hard-carrier-unions-fail-local-connectivity` gives
a rotating two-carrier counterexample to both local connectivity of the raw
union and lower semicontinuity of its simplex-coordinate refinement.
