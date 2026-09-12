# STW XXII: finite-dimensional locally trivial hyperfinite bundles

## Scope correction: recovery, not a new bundle class

Let `M` be the bounded `2`-norm-continuous section algebra of a locally
trivial tracial W*-bundle over a compact metrizable space `X` of finite
covering dimension.  If every fibre is the hyperfinite `II_1` factor, all
traces on `M` are uniform-`2`-norm continuous.  The transition cocycle may
be presented arbitrarily in `Aut(R)`.

This does not enlarge the established trivial-field class.  Evington and
Pennig prove that a locally trivial tracial W*-bundle over any compact
Hausdorff space, with every fibre isomorphic to `R`, is globally trivial;
there is no dimension hypothesis in their theorem.  They use the
Popa--Takesaki contractibility of `Aut(R)`.  Combining that theorem with
`stw22-finite-dimensional-trivial-field-traces` already gives the trace
conclusion here.

## Why global corners are unnecessary

For a spectral cut with support trace below `1/m`, cover its compact base
support by product charts and refine the cover into `d+1` discrete
families.  In each chart independently choose `m` orthogonal trace-`1/m`
corners and use the all-degree weighted-purification theorem on the closed
support of the subordinate partition function.

After multiplication by the square root of that partition function, each
local purification extends by zero to a global section.  Same-colour
supports are disjoint.  Therefore, at each point and for each colour, all
active range projections come from one chart and are orthogonal.  Different
colours need not have compatible corners; their positive range sums are
bounded separately and contribute only the factor `d+1`.

Thus the usual replication estimate survives unchanged:

```text
m sigma(c)<=(d+1)||sigma||.
```

Letting `m` grow kills every bounded trace on every norm/2-norm fibre gap.
The abstract fibre-gap criterion then disintegrates every trace against the
canonical fibre traces.

## Cocycle audit

An `Aut(R)` transition map preserves multiplication, adjoints, operator
norm, the unique trace, support trace, and orthogonality.  The local section
constructed in a chart is viewed intrinsically before extension by zero,
so no equality between independently selected witnesses on chart overlaps
is required.  The disjoint-colour formula is consequently cocycle
invariant.

The theorem assumes genuine local triviality in the continuous W*-bundle
category.  It makes no assertion for arbitrary non-locally-trivial
hyperfinite bundles or for infinite-dimensional bases.

The value of the argument is therefore proof technology: it obtains the
replication estimate directly from local charts without constructing the
global gauge.  It may transfer to locally trivial factor bundles with a
noncontractible structure group, provided the same local weighted
purification theorem is available.

## Source boundary

- S. Evington and U. Pennig,
  [*Locally Trivial W*-Bundles*](https://arxiv.org/abs/1601.05964),
  Theorem 4.10: every locally trivial tracial W*-bundle over a compact
  Hausdorff base with all fibres `R` is globally trivial.
