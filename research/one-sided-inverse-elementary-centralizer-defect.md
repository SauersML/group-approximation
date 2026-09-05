---
rg: 2
id: one-sided-inverse-elementary-centralizer-defect
kind: claim
title: A one-sided inverse gives a rank-four compressor whose defect is the complementary idempotent
distinct_from:
  generic-leavitt-self-compression-full-mf-radical: that needs a full binary Leavitt family, rank at least sixteen, and Kazhdan hypotheses, and concludes the MF radical; this is the rank-four matrix identity that needs only `ts = 1` and concludes nothing analytic.
  full-leavitt-idempotent-defect-saturation: that propagates a complementary root through the rank-20 Steinberg group once it is in hand; this produces the root as a compression defect from one elementary centralizer in rank four.
  binary-leavitt-algebra-not-directly-finite: that is the ring fact `t_0 s_0 = 1 ≠ s_0 t_0` in one algebra; this is what any such one-sided inverse does inside the elementary group.
artifacts:
  - research/artifacts/full-complementary-idempotent-check-2026-09-05.md
  - GroupApproximation/Leavitt/RankFourCompressors.lean
  - non_mf_groups_exist.tex
---

Let `R` be a unital ring with `ts = 1`, and put `e = 1 - st`, so `e² = e`
and `es = te = 0`.  In `EL_4(R)`, with `EL_3(R)` on coordinates `1,2,3`:

* `u = u_3 u_2 u_1`, `u_i = e_{4i}(t-1) e_{i4}(1) e_{4i}(s-1) e_{i4}(-t)`, is
  elementary and satisfies `u · diag(A,1) · u⁻¹ = diag(e I_3 + s A t, 1)`;
  so `u e_{ij}(a) u⁻¹ = e_{ij}(sat)` and `u` compresses `EL_3(R)` into
  itself, strictly when `e ≠ 0`.
* `c = [e_{41}(e), e_{14}(t)] = diag(1,1,1,1+et)` is elementary and
  centralizes `EL_3(R)`.
* `u c u⁻¹ = e_{12}(e)` and `[u c u⁻¹, e_{23}(1)] = e_{13}(e)`.

So for every `n ≥ 4` the root `e_{13}(e)` lies in the compression defect
`D_{EL_n(R)}(EL_3(R))` of the manuscript's Theorem A, with compressor `u`,
centralizer `c`, and source element `e_{23}(1)`.  The compressor is the comb
word of `RankFourCompressors.lean` (`compressor`, `compressor_val`, with the
Leavitt family's `p1` in the role of `e`); the centralizer word and the
defect identity are new.
