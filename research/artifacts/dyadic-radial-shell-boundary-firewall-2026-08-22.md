# Dyadic radial-shell boundary firewall — 2026-08-22

## Result

The most canonical amplified graph-of-groups model still cannot approach
the dyadic edge coupling.  Arbitrary finite mixtures of genuine spheres
about the two endpoints of the Bass--Serre edge lose at least one third of
their points when their oriented Iwahori orbit sheets are matched.

For the two depth-`n` Iwahori orbits `L_n,R_n`, both of size `2^n`, radial
shell multiplicities `a_n,b_n` give the mismatch

```text
M=sum_n 2^n(|a_n-b_(n+1)|+|a_(n+1)-b_n|).
```

The variables form two alternating weighted rays.  Edge weights are
`1,2,4,...`, while vertex weights are `1,3,6,12,...`.  Their weighted
Cheeger constant is `1/3`, and therefore `M >= (D_0+D_1)/3`.  At equal
dimension, at least one third of each model must be discarded.

This explains, in an exact dimension-free form, why replacing tree balls
by annuli, long shell windows, or huge multiplicities does not cure the
positive boundary density.  The exponential shell growth defeats the
one-dimensional plateau.

## Scope

The theorem concerns the canonical radial construction and exact matching
of oriented Iwahori orbit sheets.  The open random-lift claim allows
arbitrary finite `C_2*C_3` actions and only Hamming-almost agreement of the
two edge generators.  Such a model need not contain a large exactly matched
radial subaction.  Accordingly this result is wired as a firewall, not as a
refutation of dyadic action soficity.

