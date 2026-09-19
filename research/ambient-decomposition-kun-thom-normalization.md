---
rg: 2
id: ambient-decomposition-kun-thom-normalization
kind: claim
title: Kun--Thom centralizer normalization with property (T) of the ambient group replaced by an ambient expander decomposition of the given sofic representation
distinct_from:
  kun-thom-sofic-centralizer-normalization: that assumes property (T) of the ambient group, which yields an ambient expander decomposition for every sofic representation; this assumes only the decomposition, for the one representation at hand, so it applies to non-Kazhdan compressor groups such as ascending HNN quotients.
  bounded-cluster-period-preserves-kazhdan-fixed-algebras: that is the established fixed-algebra version (Proposition 3.1 level) together with a construction of the decomposition; this is the centralizer version (Theorem 4.1 level), which needs the cluster-groupoid half of Kun--Thom Section 4.
  relative-normalization-modulo-kazhdan-kernel: that keeps both groups Kazhdan and relativizes the centralizer modulo a normal Kazhdan subgroup; this keeps the exact centralizer and weakens the hypothesis on the ambient group.
  kt-per-compressor-assembly-over-cluster-frames: that is the Lean sequential assembly for Kazhdan pairs, quantified over all sofic approximations; this is a per-representation statement whose ambient hypothesis is a decomposition of that representation alone.
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
  - research/artifacts/kun-thom-2608-06222-section4-ambient-audit.md
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyCore.lean
---

**OPEN.** Statement (KT\*). Let
- `Gamma` be a Kazhdan group, infranormal in a finitely generated group `H`;
- `sigma : H -> S_U` be a sofic representation;
- `T` be a finite generating set of `H`, such that after `o_U(|Y_n|)` edge changes the
  `T`-generator graph of `sigma` is a disjoint union of graphs with uniform positive
  Cheeger constant.

Then `sigma(H)` normalizes `C_(S_U)(sigma(Gamma))`.

When `H` is Kazhdan, the decomposition hypothesis holds by [13, Theorem 1], and (KT\*) is
Kun--Thom Theorem 4.1. The new content is the case where `H` is not Kazhdan. The main
instance is `H = <L, u>` for a compressor `u` of a Kazhdan `L`, with the decomposition
supplied by `bounded-cluster-period-preserves-kazhdan-fixed-algebras` (item 2)
under bounded cluster period.

## Evidence (proof inspection, not a verbatim import)

The source was read from arXiv:2608.06222v1 (HTML), Section 4. The statement of Theorem 4.1
assumes "both Γ and G have Kazhdan's property (T)". In the proof, property (T) of `Gamma`
is used for [13, Theorem 1] and for the cluster groupoid of [1]. Property (T) of `G` enters
only through the ambient partition, and only in two places:

> Lemma 4.3, proof: "Before choosing the cluster scale, apply the quantitative component
> matching used in the proof of Proposition 3.1 to the full partitions
> {u_nQ_{n,i}:i∈I_n^0} and {Q_{n,j}:j∈I_n^0}."

> Lemma 4.4, proof: "Let 𝒜_n be the component partition of the edited G-generator graph.
> Its components have Cheeger constant bounded below by h_G>0. We keep this ambient
> decomposition on the original set Y_n."

Proposition 3.1 itself (verbatim in the artifact) already takes the ambient decomposition
as a hypothesis, not property (T) of `G`. The final step of Theorem 4.1 applies Lemma 4.4
to two functions:
- the orbit size `o_n`, with `o_n(pi(i)) <= (1+kappa_n) o_n(i)`;
- the isotropy order `k_n`, with `k_n(pi(i)) <= k_n(i)` from the faithful functor
  `C_n(pi(i),pi(i)) -> P(i,i) ≅ C_n(i,i)`.

Neither step uses (T) of `G` beyond `𝒜_n`.

**Lean corroboration.** In
`GroupApproximation/KunThom/CompressorNormalizationAssemblyCore.lean`,
`seqNormalizes_distinguished_of_guardedSteps` uses its hypothesis
`hTG : HasKazhdanPropertyT G` only in the argument
`(fun A ↦ exists_compressorDecomposition hTG hTΓ (normalizedSetup C hembed) A)`, which
produces the gamma and ambient decompositions. The remaining inputs `hmatching`, `hrep`,
`hfunctor` and `hhamming` are stated over an arbitrary `CompressorDecomposition`. However,
the Lean conclusion `SeqNormalizes` quantifies over all sofic approximations. So it gives
(KT\*) only for groups all of whose approximations carry an ambient decomposition, and not
per representation.

**What would establish it.** Either:
- a written line-by-line audit of Kun--Thom Section 4 confirming the two uses above are
  the only ones; or
- a per-approximation restatement of the Lean assembly with the decomposition as data.

Until then this node stays OPEN.

## Why it matters

Together with the established fixed-algebra criterion, (KT\*) yields
`bounded-period-compressors-carry-no-sofic-defect`. That turns the sofic kill of
compression defects from a statement about Kazhdan compressor groups into one about a
combinatorial invariant, the cluster period of each compressor.

## Attempts

**Attempt 1 (swarm-0917-w16-w16-titz-pull, 2026-09-19, operator-algebras): the line-by-line
audit, written as route `ambient-decomposition-kun-thom-normalization-audit`.**

Source. The whole arXiv e-print LaTeX of 2608.06222v1 was re-read: Sections 2–4, lines
395–1362. Verbatim excerpts with line numbers are in
`research/artifacts/kun-thom-2608-06222-section4-ambient-audit.md`.

Findings:
- In Section 4, "(T)" occurs only in the statement, `h_G` only at line 1033, and the ambient
  partition only at lines 857 and 1031–1084.
- The partition enters through the Proposition 3.1 matching (Lemma 4.3) and Lemma 4.4. Both
  times it enters only through:
  - (AP1), a crossing count;
  - (AP2), the summed median inequality from Lemma 2.3.
- The route proves the two missing links:
  - the decomposition hypothesis gives (AP1) and (AP2) for `T`;
  - (AP1) and (AP2) transfer between finite generating sets by word paths, with constant
    `c/(|R|L')`.

  The transfer is needed because Kun–Thom's ambient generating set `S_Γ ∪ {t_ℓ^{±1}}`
  depends on the chosen compressor family.

The Lean assembly (`seqNormalizes_of_compressor_of_steps`, line 168) is independently
per-approximation. It corroborates the audit but is not imported.

The route has `requires: []`, and its trust surface is the preprint already imported by
`kun-thom-sofic-centralizer-normalization-citation`.

The route does not re-check any step of the proof. It checks which hypothesis each step
consumes.
