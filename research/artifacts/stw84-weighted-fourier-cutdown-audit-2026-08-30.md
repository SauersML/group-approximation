# Audit: weighted Fourier cutdowns and the canonical-row order-zero gap

Date: 2026-08-30

## Positive weighted retraction

The carrier equations imply that its square root fixes every selected
augmentation coefficient on both sides.  Operator Holder continuity of the
square root converts
`||alpha^k(h)-h||<=|k|/N` into a `sqrt(|k|/N)` estimate.  Moving the right
square root across `U^k` then proves the monomial estimate, and summing gives
the Fourier-polynomial estimate.  No support projection, inverse spectral
gap, or approximate Rokhlin projection is used.

## Row-map firewall

The row formula in `(WFC4)` is a Stinespring formula and its value at the
unit is exactly `h`, so it is c.p.c.  A balanced pair of complementary
diagonal projections maps to two nonzero scalar multiples of the same
positive contraction.  Their product has norm asymptotic to `1/4`, whereas
an order-zero map must send the pair to orthogonal elements.  The elementary
two-term perturbation estimate gives distance at least `1/9`, uniformly in
the matrix size, the ambient algebra, the unitary, and the spectrum of the
carrier.

This check also explains why quasicentrality does not help the canonical
row: the diagonal matrix positions are sent to maximally overlapping copies
of the same carrier.  The obstruction survives on the scalar matrix corner
of every coefficient-valued band factorization.

## Boundary of the result

The theorem supplies a quantitative c.p. retraction of every finite Fourier
packet but not a nuclear-dimension approximation.  The fixed gap excludes
repairing the standard unsplit row into one order-zero colour.  It does not
exclude a new multi-colour factorization whose individual matrix blocks
avoid this scalar-row restriction.  Constructing such a uniformly bounded
split is the remaining exact hinge.
