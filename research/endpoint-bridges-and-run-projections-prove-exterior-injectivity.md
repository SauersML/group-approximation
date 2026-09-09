---
rg: 2
id: endpoint-bridges-and-run-projections-prove-exterior-injectivity
kind: route
title: Eliminate endpoint bridges and close the remaining run projections
target: omega-corrected-deletion-passes-full-boundary-exterior-test
requires:
  - two-sided-exterior-kernels-must-be-periodic-and-asymmetric
artifacts:
  - research/artifacts/kaplansky-omega-corrected-deletion-full-exterior-injectivity-2026-09-08.md
  - research/artifacts/kaplansky-exterior-kernels-reduce-to-pure-periodic-tails-2026-09-08.md
---

Use the proved periodic and constant-core reductions to write
the remaining source through a scalar tensor W on zero-run
endpoints. Its contraction image is invariant under K and L,
and W identifies that space with its dual.

The tensor equations make K^-1(L+K+I) an adjoint of L.
Idempotence gives Pi K^-1 Pi=Pi. The explicit finite bridge
series shows that the bridge kills ker L. The triangular
block form of W then makes K preserve im L, where injective
projection of last endpoints forces the bridge to vanish too.
Consequently W is symmetric and decomposes into the two
L-eigenspaces, using only zero runs preceded by at least two
ones.

Project the exact full target combination F_plus+omega F_minus
to active zero-run starts against their preceding last ones.
The two symmetric coefficient tensors must agree on length-two
zero runs, except for a possible primitive011 term. Its explicit
nonzero wedge removes that term.

The matched remaining target is

    alt((C+D) tensor (I+H)+(H+H_2) tensor I)W_2.

Projections to c-wedge-f and d-wedge-f impose the run shifts
I+R_2+R_3 and I+R_3+R_4. Disjoint images of R_2 and R_4
leave only an R_3-fixed tensor, on the unique primitive00111
core. There the target is c wedge d, which is nonzero.
Reconstruction therefore gives a zero full source.

The conclusion is complete injectivity in this exterior-square
boundary representation. The literal group-ring coefficient
equations for a split remain a separate problem.
