---
rg: 2
id: properly-infinite-unstable-length-uniformly-bounded
kind: claim
title: Exponential length of unitaries in properly infinite algebras is uniformly bounded by the length after one stabilization
distinct_from:
  stw99-problem-lxi-properly-infinite-k1-injective: LXI is the qualitative statement; this is the quantitative uniform bound, proved equivalent to it by the two routes between them.
artifacts:
  - research/artifacts/lxi-uniform-unitary-length-reformulation-2026-09-12.md
---

There is a function `F: [0,∞) -> [0,∞)` with the following property. Let `A` be a unital properly
infinite C\*-algebra and `u ∈ U(A)`. If `cel_{M_2(A)}(diag(u,1)) ≤ L`, then `cel_A(u) ≤ F(L)`.
Here `cel` is the exponential length, and it is infinite off the identity component.

By Theorem B of the artifact this is equivalent to STW Problem LXI. It is also equivalent to finiteness
of `F_A(L)` for each single properly infinite `A`, using the constant sequence algebra
`l^∞(A)/c_0(A)`. So a counterexample may be assembled from K1-injective properly infinite algebras
`A_n` and unitaries `u_n` whose stabilized length is bounded while their own length diverges.

## Attempts

- Reduction to LXI in both directions: proved (routes `stw99-lxi-from-uniform-unstable-length-bound`
  and `uniform-unstable-length-bound-from-lxi`). This decides neither.
- Lower bounds on `cel` through traces or determinants are unavailable, since properly infinite
  algebras have no bounded traces. No topological lower-bound mechanism that survives unital
  embeddings of `T_2` is known to this lane. That is the quantitative form of the detection problem
  in the LXI Attempts.
- Upper bounds: BRR Lemma 2.4(ii) gives a null-homotopy whenever some projection `p`, with `p` and
  `1-p` properly infinite and full, satisfies `||[u,p]|| < 1`. The `stw61-*` maximal-commutator
  theorems show that the free-product candidates admit no such `p` for large explicit families of
  mixed projections, so no length bound follows from that criterion there.
