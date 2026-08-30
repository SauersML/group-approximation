# STW XXII: finite-dimensional coloured weighted selection

## Conditional local input

The colouring theorem assumes exact continuous local square-root-weighted
embeddings of a small-support positive field into a fixed factor corner.
Sequential lower lifting does not automatically produce such a
parametrized local section on a positive-dimensional neighbourhood.  The
zero-dimensional proof avoids this issue by clopen approximation; it does
not establish this stronger local hypothesis.

## Dimension bookkeeping

For a base of covering dimension `d`, refine the local-lift cover into
`d+1` discrete colours and take a subordinate partition of unity.  Within
one colour the scalar supports are disjoint, so local weighted lifts add
without cross terms.  For each desired replica `j`, the `d+1` source
pieces sum back to the original spectral cut.

All range pieces for replica `j` lie in one fixed corner `e_j`.  Different
replicas use orthogonal corners.  Consequently the total range sum has norm
at most `d+1`, independently of the number `m` of replicas.  A bounded
trace therefore satisfies

```text
m sigma(c) <= (d+1)||sigma||,
```

and vanishes as `m` grows.

## Scope and obstruction

Conditional on exact local weighted corner lifting, the argument proves the
trace conclusion for trivial UHF fields over every compact metrizable
finite-dimensional base.  The coloured source decomposition bypasses the
global selection question, but it does not supply the local sections.  That
parametrized lifting property is the unresolved analytic hinge.  For
nontrivial tracial bundles, global orthogonal comparison corners are an
additional input.
