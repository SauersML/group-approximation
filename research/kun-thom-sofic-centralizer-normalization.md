---
rg: 2
id: kun-thom-sofic-centralizer-normalization
kind: claim
title: Kun--Thom normalization of permutation centralizers for infranormal Kazhdan pairs
distinct_from:
  kt-centralizer-normalization-hs: that is the open normalized-Hilbert--Schmidt analogue, in tracial matrix ultraproducts; this is the permutation theorem in the universal sofic group, proved by Kun and Thom.
  normal-closure-fixes-gamma-fixed-algebra: that is a consequence about the fixed diagonal algebra and the normal closure of Gamma; this is the centralizer normalization theorem itself, which that consequence consumes.
  kun-thom-expander-centralizer-formalized: that is the earlier Kun--Thom expander-centralizer theorem, concluding LEF of a commuting factor on a single expander; this is the 2026 normalization theorem for infranormal pairs, which needs no single expander.
  kazhdan-almost-centralizers-round-in-finite-actions: that rounds almost-centralizing permutations of one finite Kazhdan action; this is the ultraproduct normalization statement for a compressed pair.
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

**ESTABLISHED by citation.** Kun--Thom, *Nonsofic wreath products of
residually finite groups*, arXiv:2608.06222v1, Theorem 4.1, verbatim from the
source-verified record:

> Let Γ be an infranormal subgroup of G, and suppose that both Γ and G have
> Kazhdan's property (T). If σ:G→𝒮_𝒰 is a sofic representation, then
> C_{𝒮_𝒰}(σ(Γ)) is normalized by σ(G).

Here `𝒮_𝒰` is the universal sofic group, the metric ultraproduct of symmetric
groups with normalized Hamming distance. `Gamma` is infranormal when its
compression semigroup `{g : g Gamma g^-1 <= Gamma}` generates `G`.

Kun--Thom deduce Theorems A, B and C from it. Their proof runs finite-stage
median arguments on the vertex masses and isotropy orders of the cluster
groupoid of expander components (Sections 2 and 4 of the preprint).

**Use in this graph.**
`rigid-compression-defect-normalization-dichotomy` turns this into the
group-level statement `sofic-groups-kill-rigid-compression-defects`. That
statement applies Theorem 4.1 only to injective sofic representations with
canonical trace, so it is insensitive to how "sofic representation" is read.

**Trust surface.** An unrefereed preprint, read from source 2026-08-14. The
record notes that Theorems B, C, E and Corollary D are unchanged through v3.

Derivation: `kun-thom-sofic-centralizer-normalization-citation`.
