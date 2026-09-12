# Audit: bounded coordinate-colouring firewall

Date: 2026-08-30

## Quantitative check

The largest of `d` coordinate colours contains at least `n/d` indices.
Balanced complementary projections inside that colour are orthogonal, so
one order-zero return map sends them to orthogonal elements.  The weighted
averaging map sends them to scalar multiples of the same norm-one positive
contraction.  Their product has norm
`floor(m/2)ceil(m/2)/n^2`; a two-term perturbation estimate divides this by
at most two.  The elementary inequality
`floor(m/2)ceil(m/2)>=m^2/8` gives the uniform `1/(16d^2)` gap.

## Applicability to Fourier banding

Every diagonal matrix unit of the canonical weighted row maps to `h/n`.
Therefore the obstruction is insensitive to the Fourier unitary, the
coefficient algebra, approximate covariance, the carrier's finite spectrum,
and its possibly collapsing spectral floor.  Arbitrary disjoint coordinate
packets are covered; intervals and parity/checkerboard colourings are only
special cases.

## Exact boundary

The result does not cover an incoming c.p. map which duplicates or mixes a
Fourier coordinate among several colours, nor a return map whose restriction
to the diagonal is different from weighted averaging.  Nuclear dimension
allows both freedoms.  The valid conclusion is therefore that the entire
standard coordinate-colouring family cannot solve the augmentation-ideal
seam with a bounded number of colours, not that the ideal has infinite
nuclear dimension.
