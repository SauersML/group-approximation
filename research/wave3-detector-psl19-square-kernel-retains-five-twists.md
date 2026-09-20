---
rg: 2
id: wave3-detector-psl19-square-kernel-retains-five-twists
kind: claim
title: Every nonzero central five-twist of the explicit PSL2(19) triangle survives its specified PSL2(19)-squared cover
distinct_from:
  wave2-detector-psl19-perfect-first-kernel: that computes the integral homology of the first kernel of index3420; this proves twist survival at the specified intersection of two kernels of index3420 squared without constructing its massive cellular boundary
  hyperbolic-triangle-colimit-with-persistent-edge-twist: that requires survival in every finite cover; this proves survival in one additional explicitly specified nonsolvable cover only
artifacts:
  - research/artifacts/hyperbolic-rf-wave3-detectors-2026-09-20.md
  - experiments/hrf-wave3-detectors-2026-09-20/borel_square_cycles.json
  - experiments/hrf-wave3-detectors-2026-09-20/verify_cycles.py
---

Let `Λ`, `Q=PSL_2(19)`, and the two quotient maps `f_0,f_1` be exactly
those of [[wave2-detector-psl19-has-second-simple-quotient]]. Put
`M=ker(f_0,f_1)`, so `[Λ:M]=3420²`.

Every nonzero twist `c in F_5³` restricts nontrivially to `H²(M;F_5)`.
Equivalently, its central five-extension does not split over `M`.
All three twist directions survive this specified deeper cover.

The proof uses only400 permutation coordinates, obtained from the
action of `Q²` on `P¹(F_19)²`. Three explicit vectors over `F_5` have
zero sum on every edge orbit and independent moment values. A
standard-library checker verifies this certificate using integer
arithmetic, with no matrix-rank library required for the conclusion.

This does not compute `H_1(M;F_5)`, prove `M` perfect, or establish
survival in every finite cover. In particular it does not solve
hyperbolic residual finiteness.

**Status:** written proof and exact certificate independently reviewed on
2026-09-20. The reviewer replayed both the matrix computation and the
standard-library certificate checker, and checked the nonnormal subgroup
lifting and transfer arguments. No proof-assistant certification is claimed.

Proof: [[wave3-detector-psl19-square-kernel-retention-proof]].
