# Audit: stationary two-colour interval patching firewall

Date: 2026-08-30

Claim: `stw81-stationary-two-colour-interval-patching-forces-af`.

## Algebraic checks

1. Central localization preserves complete positivity and order zero.
   Products of images from two localized summands factor as the product of
   the scalar cutoffs times the product of the two fibre images.

2. A fixed nonzero fibre-colour map cannot use the same global colour on
   both overlapping base patches: its two unit images multiply to
   `g_0g_1 tensor h_l^2`, nonzero at the overlap point.

3. With only two colours, either the two fibre labels already share a
   colour on the first patch, or both labels switch colours across the
   patches and the diagonally opposite grid entries share a colour.  In
   both cases order zero forces `h_0h_1=0`.

4. Orthogonality of the positive support elements implies orthogonality of
   the full ranges.  Indeed positive images are dominated by scalar
   multiples of their support elements; polarization then covers arbitrary
   elements.

5. Once its two ranges are orthogonal, their support elements have
   orthogonal sum of norm at most one.  Thus the total return automatically
   becomes a single c.p.c. order-zero map from
   `F_0 direct_sum F_1`.  Availability of such approximations on all finite
   sets is exactly nuclear dimension zero, hence AF.

## Scope

The theorem applies to stationary tensor patching: the same two fibre maps
are copied under both scalar base cutoffs.  It also applies after a fixed
common conjugacy of the whole fibre frame.  It does not apply when the two
anchor frames are independently rotated or otherwise changed.  Constructing
such coherent varying frames is the live analytic possibility for
`C([0,1]) tensor Z` and, even more strongly, for arbitrary
upper-semicontinuous fields.

No lower bound on the actual nuclear dimension of
`C([0,1]) tensor Z` is claimed.  The result rules out a proof architecture,
not the desired inequality.

Outcome: **PASS**.
