---
title: STW XX checkpoint --- variable two-coordinate mixing tradeoff (2026-08-30)
---

## Exact two-by-two obstruction

Consider two independently variable coordinate blocks and a scalar early-
stage function `h` of oscillation `Delta`.  At a fibre where the two
coordinates attain opposite extrema, every rank-one projection has diagonal
parameter `t` and off-diagonal modulus `sqrt(t(1-t))`.  Its commutator error
`C` and pointwise mixed-trace-halving error `E` satisfy

```text
C^2+4E^2=Delta^2/4.
```

This completely audits continuous variable mixing for a fixed pair.  Exact
halving forces flat diagonal `t=1/2`, hence off-diagonal modulus `1/2` and
commutator `Delta/2`.  Making the commutator small forces `t` toward `0` or
`1`, where the mixed-trace error tends to `Delta/4`.  Changing the mixing
phase as the fibre varies has no effect on either quantity.

The same obstruction survives matrix amplification once centrality against
the constant early-stage matrix algebra is imposed: its exact commutant is
the two-by-two multiplicity algebra, reducing a half-rank projection to the
scalar calculation.

## Consequence for the positive-radius attack

Near the coincidence set, where `|h(x)-h(y)|` is small, a Fourier rotation
can indeed interpolate between block selectors at low commutator cost.  The
identity shows why that interpolation cannot also give pointwise trace
halving on separated fibres.  Thus a proof for classical Villadsen-I cannot
be obtained by choosing a clever continuous phase for pairwise rank-one
Fourier mixers.

This is an algebraic obstruction, not a topological nonexistence theorem:
continuous rank-one interpolations themselves exist.  Nor is it a negative
answer to Problem XX.  Uniform Gamma asks for smallness in the uniform
2-norm over the actual inverse-limit trace simplex, not pointwise over every
later-stage fibre.  To promote this local ellipse to a global obstruction,
one would have to prove that separated fibres remain visible with uniform
positive mass to suitable limit traces, or derive an averaged version which
cannot cancel.  General projections may also mix many coordinate and point
blocks at once rather than preserve a fixed pair.

## Trust boundary

The theorem is a direct `2 by 2` computation and uses no claim about the
canonical Cartan, Euler classes, or the structure of the full central
sequence algebra.  Its scope is deliberately limited to pointwise halving
for a fixed independently variable pair (and exact constant-matrix-central
amplifications).
