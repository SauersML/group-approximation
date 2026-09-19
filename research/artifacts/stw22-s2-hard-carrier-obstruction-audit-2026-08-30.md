# Audit: failure of the naive S2 hard-carrier multifunction

The example uses only a `2`-by-`2` rotation between two equivalent diffuse
projections and an orthogonal filler.  All carrier maps are operator-norm
continuous and all target projections have the same trace.

For every nonzero angle, the join of the two rotated carrier projections is
the full `p+w` corner, even though the carriers converge in operator norm as
the angle tends to zero.  Containing both therefore forces the fixed
transverse projection `w`, giving the quantitative lower bound
`sqrt(t)` in `2`-norm.  This verifies both conclusions:

* the raw two-branch union has arbitrarily close points which cannot be
  joined locally; and
* the simplex-coordinate intersection construction is not lower
  semicontinuous at a coincident-carrier point.

The obstruction targets only hard containment.  It leaves open a soft
spectral-carrier construction whose error relation tolerates small angles,
and it does not affect the fixed-factor `S^2` theorem based on a pointed
Jekel contraction.
