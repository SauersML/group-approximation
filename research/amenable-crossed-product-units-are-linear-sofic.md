---
rg: 2
id: amenable-crossed-product-units-are-linear-sofic
kind: claim
title: Over a minimal action of an amenable group, every GL_n of the binary crossed product is linear sofic and its full group is sofic, so in Track B the Leavitt factor is the only source of non-sofic inputs
distinct_from:
  amenable-minimal-crossed-products-have-faithful-rank-models: that gives the faithful rank model of the ring; this draws the unit-group consequence and its meaning for gate U.
  kazhdan-groups-avoid-full-groups-of-subexponential-actions: that excludes Kazhdan inputs from the full group over subexponential P; this excludes non-sofic inputs from the full group and non-linear-sofic inputs from every GL_n over any amenable P.
---

**ESTABLISHED** (lane proof, bh-algebra, elementary given the rank-model node; not reviewed).

**Claim.** Let `P` be a countable amenable group acting minimally on an infinite Cantor space `X`,
`B = LC(X, F_2) ⋊ P`, and `n >= 1`.
1. `GL_n(B)`, and so each of its subgroups, is linear sofic over `F_2` (Arzhantseva--Păunescu).
2. `[[P ⋉ X]] <= B^x`, and so each of its subgroups, is sofic.
3. Hence a finitely generated group that is not linear sofic over `F_2` never embeds in `GL_n(B)`, and a
   non-sofic group never embeds in `[[P ⋉ X]]`. In particular the finitely presented simple non-sofic
   group `L_(F_2)(1,2)^x` (`openai-leavitt-unit-nonsofic`) lies in no `[[P ⋉ X]]`. Whether it lies in some
   `GL_n(B)` is equivalent to asking whether it is `F_2`-linear sofic, which is open
   (`binary-leavitt-unit-group-is-f2-linear-sofic`).

**Proof.**
1. `amenable-minimal-crossed-products-have-faithful-rank-models` gives a unital embedding of `B` into a
   rank ultraproduct `𝓜 = ∏_ω M_(N_i)(F_2)/{rank-null}`, hence of `M_n(B)` into `M_n(𝓜)`, again a rank
   ultraproduct. A unit of a rank ultraproduct lifts to a sequence of matrices that are invertible after a
   rank-null correction, so `GL_n(B)` embeds in the metric ultraproduct of the `GL_(nN_i)(F_2)`. Nontrivial
   elements stay a positive rank distance from `1`, because the rank function is faithful. That is linear
   soficity.
2. The same Følner truncation of the orbit representation, applied to permutation matrices, gives sofic
   approximations: elements of `[[P ⋉ X]]` move orbit points by elements of a finite set, so they preserve a
   Følner set up to a proportion that tends to `0`. Faithfulness uses minimality exactly as in 1. ∎

**Lesson for general BH.** Track B's host `(B_W ⊗ L)^x` has two ingredients with complementary jobs.
- The crossed product `B_W` over an amenable Farrell--Jones group carries the programmable complexity
  (its language), but it sits under a faithful rank function. So everything it hosts alone is linear
  sofic, and its full group is sofic and has no infinite Kazhdan subgroup.
- The Leavitt factor `L` is non-sofic but fixed, so it carries no complexity.

So an input that is both complex and non-linear-sofic needs the two ingredients *interleaved*:
language-conditioned Leavitt isometries, not a product of a `B_W`-part and an `L`-part. Conversely, a proof
of gate U inside `GL_n(B_W)` alone would prove that every decidable group is `F_2`-linear sofic. That is an
open problem of its own, and it is refuted if `L_(F_2)(1,2)^x` is not linear sofic.
