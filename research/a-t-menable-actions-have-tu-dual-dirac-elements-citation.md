---
rg: 2
id: a-t-menable-actions-have-tu-dual-dirac-elements-citation
kind: route
title: Literature import of the Tu dual-Dirac factorization for a-T-menable actions, as stated and used by Baum--Guentner--Willett
target: a-t-menable-actions-have-tu-dual-dirac-elements
requires: []
---

Direct literature import. The primary source read is the arXiv text of
**BGW:** P. Baum, E. Guentner, R. Willett, *Expanders, exact crossed products, and the Baum-Connes conjecture*,
arXiv:1311.2343v3. Its text was extracted from the PDF on 2026-09-16. Quotes are verbatim up to extraction artefacts;
math symbols are transcribed.

- **Definition 6.1** is "adapted from work of Tu [49, Section 3]". Its content is the four conditions recorded in the
  target (continuity, `h(x, e) = 0`, `h(x, g) = h(xg, g^(-1))`, the negative-type inequality over `x g_i, g_i^(-1) g_j`,
  and local properness on `{x ∈ K, xg ∈ K}` for compact `K`).
- **Theorem 6.2:** "Let G be a second countable locally compact group acting a-T-menably on a second countable locally
  compact space X. The ⋊-Baum-Connes assembly map K^top_*(G; C_0(X)) -> K_*(C_0(X) ⋊_⋊ G) is an isomorphism for every
  exact and Morita compatible crossed product ⋊."
- **Proof of Theorem 6.2:**
  - the action "by [49, Proposition 3.8] acts properly by isometries on a field of Hilbert spaces";
  - "It then follows from [49, Théorème 1.1] ... that there exists a proper X ⋊ G algebra A ... and equivariant E-theory
    elements α ∈ E^G(A, C_0(X)), β ∈ E^G(C_0(X), A) such that (6.1) β ∘ α = 1 in E^G(C_0(X), C_0(X))";
  - "(Actually, Tu works in the framework of equivariant KK-theory in the reference [49] used above. Using the natural
    transformation to equivariant E-theory, we obtain the result as stated here.)";
  - for the proper algebra, "all crossed products are the same for a proper action, whence the central horizontal map
    identifies with the usual assembly map, and so is an isomorphism by [11, Théorème 2.2]".
- **Footnote 4** (proper `X ⋊ G`-algebra): there are a locally compact proper `G`-space `Z`, an equivariant
  *-homomorphism `C_0(Z) -> ZM(A)`, and an equivariant, open, continuous map `Z -> X`.
- **Remark 6.3:** Baum--Connes with coefficients holds for a-T-menable groups, for maximal or reduced crossed products
  ([30], Higson--Kasparov). Context only.
- **References as listed by BGW:**
  - [49] J.-L. Tu, *La conjecture de Baum-Connes pour les feuilletages moyennables*, K-Theory 17 (1999), 215--264.
    **Not fetched; Proposition 3.8 and Théorème 1.1 are unverified at the source.**
  - [11] J. Chabert, S. Echterhoff, R. Meyer, *Deux remarques sur l'application de Baum-Connes*, C. R. Acad. Sci.
    Paris Sér. I Math. 332 (2001), 607--610. Not fetched.

**How the target is read off.**
- The a-T-menable hypothesis and the proper algebra `A` are those of the proof of Theorem 6.2.
- The KK-level identity `β ⊗_A α = 1` is Tu's framework, as BGW's parenthetical states. BGW's displayed (6.1) is its
  image in E-theory.
- "All crossed products are the same for a proper action" and [11, Théorème 2.2] give the last sentence of the target.

**Context, not re-read.** The passage from Tu's groupoid-equivariant KK-theory for `X ⋊ G` to `KK^G`, by forgetting the
`C_0(X)`-structure, is standard (Le Gall).
