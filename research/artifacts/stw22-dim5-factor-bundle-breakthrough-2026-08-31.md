# Audit: weighted degree four and dimension-five factorial bundles

## Verdict

PASS.  The diffuse spectral-supercarrier induction advances from degree
three to four, the relative dyadic recursion advances from `B^4` to `B^5`,
and half slack puts every nonzero matrix value in the audited
codimension-two Bott-cancellation regime.

## Degree bookkeeping

```text
projection S3 lift: Michael n=2, then diffuse unitary S3 filling
carrier over S4:    Michael n=3 on Grassmannian values
pair lifts over S4: Michael n=3 on corner-unitary stabilizers
relative B5 bands:  Michael n=4 on Stiefel values
bundle over dim 5:  Michael n=4 on weighted-copy values
```

At every stage the required global connectivity is supplied by Jekel after
an uncontrolled unitary lift, while the local modulus comes from the
preceding universal Stiefel degree.  The inclusive-cutoff lower
semicontinuity proof is independent of the parameter-space dimension.

## Quantitative audit

The selected carrier has trace at most `2delta^2/kappa^2`; localized Jekel
fills remain within `2sqrt(2)delta/kappa` because the represented frame
changes only on that carrier.  With `kappa=epsilon_0/40` and
`delta=epsilon_0^2/1000000`, both this term and the direct-rotation collar
are inside the requested ball.

Row amplification is an exact isometry from the tuple Hilbert-sum metric
to the normalized first-corner metric.  With
`eta=(epsilon_0/12)^2`, the high input is
`epsilon_0^3/216000000` and the low diameter costs at most
`epsilon_0/6`.  The relative band modulus may depend on the fixed positive
trace reserve, but only existence and the universal low diameter are used;
the outer modulus is slack-independent.

## Matrix and selection audit

The matrix codimension-two four-sphere theorem includes global
fourconnectivity and the larger cubic modulus.  Under `m>=2` and half slack,
every nonzero matrix value has total rank at least two and unused rank at
least two.  Mixed factor types therefore share the diffuse modulus.

The gap proof needs only these half-slack values: for each `m>=2`, the
spectral/central cut has support below `1/(2m)`.  Stabilized lower
semicontinuity is type-free, and Michael degree four over a paracompact base
of dimension at most five gives the exact tuple.  No continuity of factor
type is used.

