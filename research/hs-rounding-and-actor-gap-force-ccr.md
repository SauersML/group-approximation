---
rg: 2
id: hs-rounding-and-actor-gap-force-ccr
kind: claim
title: Stable vertex rounding plus a center-compatible coarse actor gap at compressor generators forces compressor commutant rigidity
distinct_from:
  hs-normalization-needs-coarse-actor-scale-pinning: that is the open conditional with hypotheses (H1)-(H3) at an unspecified generating set; this is the corrected conditional (H1)+(H2'), proved, with (H3) dropped and the block/center clause taken uniformly over block-dependent central contractions.
  vertex-rounding-reduces-ccr-to-commutant-excess: that reduces (CCR) under (H1) to a finite commutant excess and supplies the intertwiner; this consumes both and proves the excess vanishes once the coarse actor gap is added.
  tracial-median-concentration: that is the median output of the nested abelian block decomposition, where the observable is a function of the blocks; this runs the median step on isotypic aspect ratios over coarse actor blocks that do not contain the observable.
artifacts:
  - research/artifacts/hs-s4-assembly-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma < G` be an infranormal pair of Kazhdan groups, with `(F, kappa)` a Kazhdan
pair for `Gamma`. Let `t_1, ..., t_k` be strict compressors with `G = <Gamma, t_1, ..., t_k>`, and put
`Lambda_i = t_i Gamma t_i^(-1)` and `S = F cup {t_i^(+-1)}`. Let `sigma : G -> U(prod_U M_n)` be trace-preserving,
with coordinates `sigma_n`. Assume, along `U`:

- **(H1)** After `o(n)` padding there are genuine `pi_n : Gamma -> U(n')`, `n'/n -> 1`, with
  `max_(s in F) ||sigma_n(s) - pi_n(s)||_2 -> 0`.
- **(H2')** There are orthogonal projections `q_A` with `p = sum_A q_A` such that:
  - (a) `tau(1 - p) -> 0`, and `sum_A ||[sigma_n(s), q_A]||_2^2 -> 0` for each `s in S`;
  - (b) the compressed tuples `a_(A,s) = q_A sigma_n(s) q_A`, `s in S`, satisfy one scalar adjoint gap
    `kappa' > 0` on every block, in the sense of `median-poincare-concentration`;
  - (c) `sup sum_A ||[q_A, z_A]||_2^2 -> 0`, the supremum over all families of contractions
    `z_A in Z(pi_n(Gamma)')` chosen block by block.

Then, for each `i`, `sigma(Lambda_i)' cap M = sigma(Gamma)' cap M` (CCR), and `sigma(G)` normalizes
`sigma(Gamma)' cap prod_U M_n`, i.e. the conclusion of `kt-centralizer-normalization-hs` holds for `sigma`.

**How the proof goes** (`hs-rounding-and-actor-gap-force-ccr-proof`, full detail in the artifact):
1. **The observable.** Build the median observable
   `f = sum_A q_A F_(m_A)(zeta_A) q_A + (1/2)(1 - p)`, with `F_a(x) = x/(x+a)`, `zeta_A` the aspect ratio of
   `pi_n(Gamma)'`, and `m_A` chosen so that `1/2` is a median on block `A`.
2. **Vertex generators.** The error `sigma_n(s) - pi_n(s)` factors on one side, so block-dependent scales
   sum.
3. **Compressors.** Through the intertwiner `v` there is an exact operator inequality
   `F_a(sigma_n(t) zeta_A sigma_n(t)^*) >= v Q F_a(zeta_B) Q v^* - c/4`, valid for all `a` at once, with
   `||vQ - 1||_2 -> 0`. Trace conservation turns it into almost invariance of `f`, and into
   `tau(f_B - f) -> 0` for the same observable built from `zeta_B`.
4. **Concentration and conclusion.** `median-poincare-concentration` on each block pins `f` at `1/2`.
   With (c), this bounds the jump mass `tau(zeta_B >= (1+c) zeta_A)`. The excess lemma then gives (CCR).

**Scope.**
- This is a conditional theorem for one `sigma`. It does not decide `kt-centralizer-normalization-hs`.
- The open inputs, for every model, are `hs-stable-vertex-rounding-for-every-model` (H1) and
  `hs-coarse-actor-gap-at-compressor-generators` (H2').
- No root is affected.
