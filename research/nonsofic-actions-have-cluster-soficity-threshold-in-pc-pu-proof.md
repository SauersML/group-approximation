---
rg: 2
id: nonsofic-actions-have-cluster-soficity-threshold-in-pc-pu-proof
kind: route
title: Factor the action out of its Bernoulli product and compress the orbit relation above p_u
target: nonsofic-actions-have-cluster-soficity-threshold-in-pc-pu
requires:
  - fpbs-cluster-count-trichotomy
  - fpbs-critical-no-infinite-cluster
  - uniqueness-phase-cluster-relations-inherit-nonsoficity
artifacts:
  - research/artifacts/percolation-soficity-threshold-2026-09-12.md
  - research/artifacts/percolation-soficity-threshold-actions-2026-09-12.md
---

Proof in Section 5 of the part 2 artifact, using the lemmas of Section 1 of part 1.

1. **Space.** `X x [0,1]^E` with the diagonal action is free, since the second factor is free. It is
   ergodic, since `a` is ergodic and the Bernoulli factor is mixing.
2. **Factor lemma (part 2, Lemma 5.1).** `L^inf(X)` and `u_g` generate a trace-preserving copy of
   `L(R_a)` inside `L(R_(a x B))`. Full group elements `x -> c(x).x` lift to `(x,xi) -> c(x).(x,xi)`. So
   soficity of `R_(a x B)` restricts to soficity of `R_a`, and `R_(a x B)` is nonsofic.
3. **Below `p_c` and monotonicity.** The relations increase with `p`, and classes below `p_c` are finite.
   At `p_c` on nonamenable graphs they are finite by `fpbs-critical-no-infinite-cluster`. This is part 1,
   Lemmas 1.1 and 1.5.
4. **Above `p_u`.**
   - By `fpbs-cluster-count-trichotomy`, `R^a_p` on `X x A_p` equals `R_(a x B)` restricted there.
   - Restriction (Lemma 1.2) and amplification (Lemma 1.3) are the permanence steps proved in part 1 for
     `uniqueness-phase-cluster-relations-inherit-nonsoficity`. They transfer nonsoficity from
     `R_(a x B)` to `R^a_p`.
