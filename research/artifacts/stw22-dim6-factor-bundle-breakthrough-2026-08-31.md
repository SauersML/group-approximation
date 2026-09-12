# Audit: weighted degree five and dimension-six bundles

## Verdict

PASS.  Diffuse spectral supercarriers bootstrap formally through degree
five.  The matrix branch requires codimension three; a skeleton carrier
cancels `c_1,c_2`, and the sole unstable localized `pi_5` case is a
rank-two-complement `Z/2`, killed by promoting that entire complement.

## Index audit

Projection `S^4` lifts use Michael `n=3`; the carrier and pair lifts over
`S^5` use `n=4`; relative bands over `B^6` use `n=5`; stabilized bundle
selection over dimension six uses `n=5`.  Each stabilizer degree is supplied
by the preceding diffuse Stiefel theorem.

## Matrix audit

The rank-`6K` carrier is built on the two-skeleton.  A determinant line
kills `c_1`; after extension to the four-skeleton, the complement splits as
a rank-two bundle plus trivial lines, and promoting the rank-two bundle
kills `c_2`.  This nullifies every five-cell boundary in its containing
Grassmannian.  For localized pairs, codimension three makes the Stiefel
fibre vanish through `pi_5`; the unitary exact sequence leaves only the
`pi_4(U(2))=Z/2` complement-rank-two anomaly, removed without changing the
frame.  The final carrier has rank at most `11K`, giving the stated radius.

## Selection audit

Half slack with `m>=3` forces every nonzero matrix value to have target
codimension at least three.  The gap proof may let `m` tend to infinity
through integers at least three, so this restriction costs nothing.
Relative low-band moduli may depend on the fixed trace reserve, but their
output diameter is universal; row amplification therefore retains the
factor-uniform cubic modulus.

