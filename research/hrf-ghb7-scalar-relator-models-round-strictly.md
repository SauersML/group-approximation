---
rg: 2
id: hrf-ghb7-scalar-relator-models-round-strictly
kind: claim
title: The GHB7 Schur multiplier has exponent dividing 2401 and sufficiently small globally scalar relator defects round in the original dimension
distinct_from:
  hrf-ghb7-scalar-expander-rounding: That is open for arbitrary small matrix-valued defects on expanding tuples; this proves rounding without expansion when every defining relator is exactly scalar.
  hrf-audit-projective-internality-does-not-round: That produces nonroundable projective models for certain Kazhdan central covers; this uses the finite Schur multiplier of the ambient GHB7 group to exclude such globally scalar defects for GHB7 itself.
  finite-multiplier-projective-models-round-strictly: That is a general qualitative projective-rounding theorem under finite homology hypotheses; this computes the GHB7 integral multiplier as a vertex sum and gives a dimension-free explicit scalar-relator threshold and correction bound.
artifacts:
  - research/artifacts/hyperbolic-rf-ghb7-2026-09-20.md
---

Let G=G_HB2(7), with vertex groups X_0,X_1,X_2 and its standard
eleven-relator presentation. Then the three inclusions induce

    H_2(G;Z) ≅ H_2(X_0;Z) direct-sum H_2(X_1;Z) direct-sum H_2(X_2;Z),

so H_2(G;Z) is finite and killed by 2401.

Suppose A,B,C in U(d) evaluate every defining relator r to an exact
scalar lambda_r I. Put delta=max_r |lambda_r-1|. If

    delta < 2 sin(pi/2401),

all eight commutator relators already evaluate to I. Multiplying A,B,C
by scalar seventh roots near 1 then gives a genuine representation
pi:G->U(d), with generator errors <=(pi/14)delta in operator norm
and normalized HS norm. There is no change of dimension.

For the doubled fourteen-relator presentation, the same exact-scalar
hypothesis yields errors <=(1+pi/14)delta on all six entries.

The artifact reconstructs the known qualitative finite-multiplier
rounding principle in the scalar-relator language. The specialized
integral calculation and quantitative bound are the content of this node.

**Boundary.** Approximately scalar relators do not meet this hypothesis.
The positive-b_2 congruence kernel does not meet the finite-multiplier
hypothesis. Its induced models can have nonscalar block defects.
GHB7 flexible HS stability and hyperbolic residual finiteness remain open.

DERIVATION
hrf-ghb7-scalar-relator-rounding-proof
