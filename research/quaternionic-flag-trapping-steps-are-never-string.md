---
rg: 2
id: quaternionic-flag-trapping-steps-are-never-string
kind: claim
title: No quaternionic partial flag manifold with Q a sum of tautological multiples is a string trapping step with nonzero Euler count
distinct_from:
  quaternionic-grassmannian-trapping-defect-is-rank: That computes the defect k·q_1 of Grassmannian steps, which vanishes mod k; this shows that no partial flag manifold of Sp(n), with Q built from tautological blocks, has defect exactly zero together with a nonzero count.
artifacts:
  - research/artifacts/class-four-lambda-mod-eight-trapping-part4-2026-09-13.md
---

Let F = Sp(n)/(Sp(k_1) x ... x Sp(k_s)) with s >= 2, and let zeta_i be its
tautological quaternionic bundles of rank k_i. Take a protected rank
p >= 1. Put Q = (+)_i d_i·zeta_i with d_i >= 0 and W = Hom(Q, C^p). Assume
dim_R F = rank_R W, so the locus is zero-dimensional. Then the following
cannot hold simultaneously:

- lambda(TF) = lambda(W_R) in H^4(F; Z), that is, TF − W_R is string;
- <e(W_R), [F]> != 0.

So string (tmf-type) trapping detectors cannot be built from quaternionic
flag steps with tautological Q. The mod-m version does hold for
Grassmannians: defect k·q_1 is 0 mod k.

Complete argument. Not independently reviewed.
