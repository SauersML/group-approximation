# STW XXII: zero-dimensional weighted corner selection

## Problem with selecting supports

For a `2`-norm-continuous positive field, spectral support projections can
jump discontinuously.  Selecting those projections or their unweighted
partial isometries continuously is therefore too strong.

## Weighted replacement

If all supports have trace strictly below the trace of a fixed factor
corner, the operators

```text
u d^(1/2)
```

with range in that corner admit local `2`-norm lifts.  A high/low spectral
split aligns the high part; the strict trace slack places the remaining
support in the unused part of the corner; and the square root makes the
low part small in `2`-norm.  Clopen refinement turns these local lifts into
a global section over any compact metrizable zero-dimensional base.

## Consequence

Every sufficiently small spectral cut in a trivial hyperfinite-factor field
has arbitrarily many continuous orthogonal equivalent copies in its fibre
gap.  Hence every bounded trace on every gap vanishes.  This includes the
nonzero escaping-rank quotient at `[0,omega^omega]`: limit
Cantor--Bendixson rank creates a nonzero norm quotient but not a singular
trace in the trivial-field model.

The use of fixed corners is specific to a globally trivial factor field.
For a nontrivial bundle, choosing such corners globally is an additional
bundle problem and is not covered by this argument.
