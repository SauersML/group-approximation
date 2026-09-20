---
rg: 2
id: wave4-detector-psl19-borel-a4-sector-proof
kind: route
title: Compute the exact5700-point Borel-times-A4 cover and identify its invariant cohomology sector
target: wave4-detector-psl19-borel-a4-sector-vanishes
requires:
  - wave2-detector-psl19-has-second-simple-quotient
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-detectors-2026-09-20.md
  - experiments/hrf-wave4-detectors-2026-09-20/borel_a4_homology.py
  - experiments/hrf-wave4-detectors-2026-09-20/borel_a4_homology_result.json
---

All matrices are taken modulo scalar sign in `SL_2(F_19)`.
Put `i=[[0,1],[-1,0]]`, `j=[[1,6],[6,-1]]`, and
`h=(-I+i+j+ij)/2`. Exact enumeration verifies
`A=<i,j,h>` has order twelve. `B` has order171. Hence
`X=Q²/(B×A)=P¹(F_19)×Q/A` has5700 elements.

The three edge permutations use matrix pairs
`(x12,x12)`, `(x13,x13)`, `(x23,u^-1 x23 u)` from the required
explicit quotient. Every edge orbit has length five. Each vertex
has three orbits of sizes3420,1140,1140, hence stabilizers of
orders1,3,3. Thus every cell stabilizer for the action of `K`
on the contractible triangle development has order prime to five.
The equivariant cellular spectral sequence therefore identifies
its mod-five group homology with the ordinary homology of the
finite quotient complex.

This complex has nine vertices,3420 edges and5700 faces. Build an
actual spanning tree on its nine vertices and remove the eight
tree-edge rows. Each face boundary has coefficients `(+1,-1,+1)`
in edge types `(12,13,23)` before that removal. The resulting
`3412×5700` boundary matrix has rank3412 over `F_5`.

The recorded computation performs2912 invertible sparse pivots,
leaving a `500×2788` matrix of rank500. Each pivot subtracts a
multiple of its column from every other column incident at the
pivot row, then removes the isolated pivot row and column. These
are invertible elementary operations and contribute exactly one
to rank. Empty columns can be removed without altering rank.
The final finite-field rank is computed by python-flint. An
independent reviewer checked all indexing, signs and pivot updates
and reran the entire script with the same output.

Therefore `H_1(K;F_5)=0` and `dim H_2(K;F_5)=5700-3412=2288`.
In `1→M→K→B×A→1`, the quotient has order2052 prime to five.
Averaging kills positive-degree quotient cohomology with any
`F_5` module, so restriction gives
`H¹(K;F_5) ≅ H¹(M;F_5)^(B×A)`. This proves precisely the stated
sector vanishing, with no conclusion about other composition
factors of `H¹(M;F_5)`.
