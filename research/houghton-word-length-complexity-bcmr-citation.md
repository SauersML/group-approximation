---
rg: 2
id: houghton-word-length-complexity-bcmr-citation
kind: route
title: Import Burillo–Cleary–Martino–Röver's word-length estimate for Houghton groups
target: houghton-word-length-is-complexity-up-to-log
requires: []
---

Citation import, not a reproof. J. Burillo, S. Cleary, A. Martino and
C. E. Röver, *Commensurations and metric properties of Houghton's groups*,
arXiv:1403.0026v2 (22 Feb 2016), Section 4, read from the arXiv PDF on
2026-09-19. The text layer of the PDF reads, verbatim (up to extraction
spacing):

> "Given σ ∈ H_n, we define p_i(σ), for i ∈ Z_n, to be the largest integer
> such that (i, p_i(σ))σ ≠ (i, p_i(σ) + t_i(σ)). [...] The complexity of
> σ ∈ H_n is the natural number P(σ), defined by P(σ) = Σ_{i∈Z_n} p_i(σ)."

> "Theorem 4.1. Let n ≥ 3 and σ ∈ H_n, with complexity P = P(σ) ≥ 2. Then
> the word length |σ| of σ with respect to any finite generating set
> satisfies P/C ≤ |σ| ≤ KP log P, where the constants C and K only depend on
> the choice of generating set."

> "Proof. [...] we can and will choose {g_ij | i, j ∈ Z_n, i ≠ j} as
> generating set to work with, and show that the statement holds with C = 1
> and K = 7. The lower bound is established by examining how multiplication by
> a generator can change the complexity. [...] Thus |P(σg_ij) − P(σ)| ≤ 1,
> which establishes the lower bound."

The same paper (Section 5) records: "A natural, but seemingly difficult,
question is whether H_n is distorted in H_m for 3 ≤ n < m."

Reading conventions. Rays are indexed by `Z_n` there and by `{1, ..., n}`
here. For a ray on which `σ` is the identity no integer satisfies the
defining inequality; we take `p_i = 0`, which is the reading under which
"an element with complexity zero is trivial" (loc. cit.) holds.
