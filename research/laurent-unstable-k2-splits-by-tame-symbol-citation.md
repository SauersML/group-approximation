---
rg: 2
id: laurent-unstable-k2-splits-by-tame-symbol-citation
kind: route
title: Import Kunyavskii--Lavrenov--Plotkin--Vavilov, Lemmas 3.1, 3.2 and 6.3 of arXiv:2307.05526v2
target: laurent-unstable-k2-splits-by-tame-symbol
requires: []
---

Citation import. B. Kunyavskiĭ, A. Lavrenov, E. Plotkin, N. Vavilov, *Bounded generation of Steinberg
groups over Dedekind rings of arithmetic type*, arXiv:2307.05526v2 [math.KT], 19 Jul 2023. The PDF was
fetched on 2026-09-17 and its text extracted with pypdf. Quotations are verbatim up to extraction of
symbols (`k∗` is `k^*`, `֒→` is an injection).

- **Definition (§3).** "Following [St78], we denote K2(Φ , R ) = Ker ( St(Φ , R ) → Gsc(Φ , R ) )."
  Also: "for two invertible elements u, v ∈ R∗ we deﬁne the Steinberg symbol
  {u, v }α = hα(uv)hα(u)−1hα(v)−1."
- **Lemma 3.1.** "For a ring R and a reduced irreducible root system Φ elements {u, v }α for
  u, v ∈ R∗, α ∈ Φ , are central in St(Φ , R ) and belong to K2(Φ , R )."
- **Lemma 3.2** (attributed to Matsumoto, [Mat, Corollaire 5.11]). "Let k be a ﬁeld, Φ be a reduced
  irreducible root system. ... 2) Let Φ be a non-symplectic reduced irreducible root system (i.e.,
  Φ ⁄= A1, B2, Cl). Consider any embedding A2֒→Φ on long roots. Then the induced map
  K2(A2, k ) → K2(Φ , k ) is in fact an isomorphism."
- **Lemma 6.3.** "For an arbitrary ﬁeld k and a non-symplectic root system Φ there is an exact
  sequence of abelian groups 0 → K2(Φ , k ) → K2(Φ , k [X, X −1]) → k∗ → 0 split by the map
  {X, −}α : k∗ → K2(Φ , k [X, X −1]) for any ﬁxed long root α ∈ Φ . In particular, the natural
  embedding induces an injective map K2(Φ , k [X, X −1])֒→K2(Φ , k (X))."
  - Its proof begins: "Since K 2(Φ , F ) = K 2(F ) for any ﬁeld F by Proposition 3.2, the second
    statement follows from the ﬁrst one." (The paper's cross-reference "Proposition 3.2" is its
    Lemma 3.2.) The first statement is cited there to "[Hur, Satz 3]" for `Φ ≠ G_2`.

**Derivation of the claim.** Take `Φ = A_(n-1)`, `n >= 3`, which is non-symplectic, with
`G_sc = SL_n`. Items 1, 2 and 4 are Lemma 6.3 and Lemma 3.1. A splitting map of an exact sequence
of abelian groups is an injective homomorphism. For item 3, the rank embeddings
`A_2 ⊂ A_(n-1) ⊂ A_n` are embeddings on long roots (all roots are long in type `A`). So by Lemma 3.2
each `K_2(3,F) -> K_2(n,F)` is an isomorphism, hence so is each `K_2(n,F) -> K_2(n+1,F)`, and
`K_2(n,F)` maps isomorphically onto the colimit `K_2(F) = ker(St(F) -> E(F))`.
