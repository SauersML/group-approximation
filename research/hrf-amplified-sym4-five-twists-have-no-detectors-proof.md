---
rg: 2
id: hrf-amplified-sym4-five-twists-have-no-detectors-proof
kind: route
title: Normalize by vertex gauges and force the unit into the span of sixty-four associators
target: hrf-amplified-sym4-five-twists-have-no-detectors
requires: []
artifacts:
  - research/artifacts/hrf-amplified-2026-09-20.md
  - research/artifacts/hrf-amplified-certificates.json
  - research/artifacts/hrf-amplified-verify.py
  - research/artifacts/hrf-amplified-linear-probe.py
---

Work over `k=F_19[z]/(z^2-4z+1)`, with `z` of order five.
After conjugating vertex one to `rho tensor I_m`, write the other
vertex maps with conjugators `U,V` and set `W=V^-1U`.
The edge equations are `UA=z^a AU`, `VB=z^b BV`, `WC=z^c CW`,
`U=VW`, for a nonzero triple `(a,b,c)` and the pinned Sym4 edge
matrices `A,B,C`. All 124 triples are handled separately.

The simple edge spectra give complete block parametrizations
`V=P_B T_b diag(V0,...,V4) P_B^-1` and
`W=P_C T_c diag(W0,...,W4) P_C^-1`, with implicit multiplicity
tensors and every block invertible. Replacing `U` by `UR` and
`V` by `VS`, where `R,S` act on multiplicities, preserves both
vertex maps and changes `W` to `S^-1 W R`. With
`S=V0^-1`, `R=W0^-1 V0^-1`, the zeroth blocks both become the
identity. This is valid without commuting any blocks.

The artifact defines the exact `25x25` scalar matrix `L` whose
equations are `L(V_i W_j)=0`. In every case a certified `4x25`
matrix annihilates its sixteen interior columns. Its four remaining
linear relations have an invertible pivot matrix and express all
eight nonconstant blocks affinely in four noncommuting elements
`x1,...,x4`. The independent verifier checks this parameterization
and its implication from the original equations.

Substituting, without commuting factors, gives all 25 equations
in the 21 words `1,xi,xixj`. Their sixteen quadratic columns have
an explicitly checked invertible minor. The supplied `16x5` table
`M` satisfies `Q_quad M+Q_low=0` for every row, so the equations
imply `xi xj=sum_h M_(ij,h)e_h` with `e0=1`, `eh=xh`.

Give the five-dimensional vector space on these `e_h` the bilinear
product specified by `M`, with `e0` a unit. Any associative-algebra
solution induces a product-preserving linear map to its target.
Consequently all sixty-four vectors
`(ei*ej)*eh-ei*(ej*eh)`, for `1<=i,j,h<=4`, must map to zero.
For each triple the certificate supplies a linear combination of
five such vectors equal to `e0`. Therefore a solution would have
`1=0`, impossible in every positive-size matrix algebra.

The standard-library verifier reconstructs Sym4 from the displayed
two-by-two edges, checks matrices and eigenbases, reconstructs all
linear equations, binds every elimination and table to them, then
recomputes the associators and verifies all 124 unit identities.
It independently returned PASS in 1.2731 seconds on MSI. The
artifact gives the complete reduction, certificate encoding, prior
method attribution, and resource receipt. No commutative Groebner
certificate or finite-dimensional bound is assumed, proving the claim.
