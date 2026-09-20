---
rg: 2
id: hrf-break-sym4-five-twists-have-no-detectors-proof
kind: route
title: Parametrize all invertible edge intertwiners and verify 124 exact polynomial certificates
target: hrf-break-sym4-five-twists-have-no-detectors
requires: []
artifacts:
  - research/artifacts/hrf-breakthrough-2026-09-20.md
  - research/artifacts/hrf-breakthrough-2026-09-20-certificates.json
  - research/artifacts/hrf-breakthrough-2026-09-20-verify.py
  - research/artifacts/hrf-breakthrough-2026-09-20-all-twists.py
  - research/artifacts/hrf-breakthrough-2026-09-20-sym4.py
---

Sections 1--3 of the artifact give the complete reduction and certificate
boundary. Write `A,B,C` for the explicit symmetric-fourth-power edge
matrices over `k=F_19[z]/(z^2-4z+1)`, where `z` has order five.
After simultaneous conjugation, the three vertex representations are
`rho,U rho U^-1,V rho V^-1`. Setting `W=V^-1 U`, their edge equations
are `UA=z^a AU`, `VB=z^b BV`, `WC=z^c CW`, `U=VW`, for a nonzero
triple `(a,b,c)`.

Each edge has five distinct eigenvalues. In its ordered eigenbasis,
every intertwiner is a fixed cyclic-shift matrix times a diagonal matrix.
Thus write `V=P_B T_b diag(v) P_B^-1` and
`W=P_C T_c diag(w) P_C^-1`. Invertibility requires all diagonal
coefficients nonzero. Scalar normalization gives `v0=w0=1` without
losing solutions. The 25 entries of `(VW)A-z^a A(VW)`, together with
`inv*prod(v1,...,v4,w1,...,w4)-1`, are therefore an exact polynomial
system for all allowable conjugators, over any extension field.

For each of the 124 nonzero triples, the attached certificate supplies
26 polynomial multipliers whose dot product with these equations is
exactly 1. The separate pure-Python verifier first reconstructs `Sym^4`
of the pinned two-by-two matrices, matches the edge matrices, independently
inverts and verifies the ordered eigenbases, and reconstructs and matches
all 3,224 conjugacy and saturation equations. It then multiplies sparse
polynomials using the displayed quadratic finite-field relation and checks
all identities and exact coverage of the 124 triples. The complete MSI
run and this independent input-bound arithmetic verification succeeded.
No scalar equivalence of triples or finite-field sampling is used.

At any purported common zero, its verified polynomial identity reads
`0=1`. This excludes the stated family over the algebraic closure and
hence over every finite extension of `F_19`, proving the claim.
