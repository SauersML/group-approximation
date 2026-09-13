---
rg: 2
id: seward-approximate-bernoulli-models-and-semicontinuity-citation
kind: route
title: Import Corollary 6.1 and Lemma 6.2 of Seward's Krieger II
target: seward-approximate-bernoulli-models-and-semicontinuity
requires: []
---

**Source.** B. Seward, *Krieger's finite generator theorem for actions of countable
groups II*, arXiv:1501.03367v4 (7 Apr 2019). Read on 2026-09-12 from the PDF text
extracted on MSI (`/projects/standard/hsiehph/sauer354/review-lit/entropy/1501.03367.txt`,
lines 319, 1288–1294 and 1358–1363). Spacing lost in extraction is restored, the
action symbol `↷` is restored from the extracted `y`, and `𝓛`, `𝓚` denote the
calligraphic partitions of the original.

- Section 2: "When G ↷ X is a Borel action, we write E_G(X) for the collection of
  ergodic invariant Borel probability measures on X."
- Corollary 6.1: "Let G be a countably infinite group and let G ↷ (X,µ) be a free
  p.m.p. ergodic action. Let (L,λ) be a probability space with L finite. Let 𝓛 be
  the canonical partition of L^G, and let 𝓚 be a partition coarser than 𝓛. If
  h^Rok_G(X,µ) < H(𝓛|𝓚), then for every open neighborhood U ⊆ E_G(L^G) of λ^G and
  every ε > 0, there is a G-equivariant isomorphism φ : (X,µ) → (L^G,ν) with ν ∈ U
  and h^Rok_{G,ν}(𝓚^G) < ε."
- Lemma 6.2: "Let G be a countable group, let L be a finite set, and let L^G have
  the product topology. Let C be a countable collection of clopen sets, and let F be
  the smallest G-invariant σ-algebra containing C. Then the map µ ∈ E_G(L^G) ↦
  h^Rok_G(L^G,µ|F) is upper-semicontinuous in the weak*-topology."

**Specialization.**
- Item 1 of the target: take `𝓚 = {L^G}`. Then `H(𝓛 | 𝓚) = H(𝓛) = H(λ)`, and
  `𝓚^G` is the trivial σ-algebra.
- Item 2 of the target: take `C = ∅`. Then `F` is the trivial σ-algebra, and Rokhlin
  entropy relative to it is Rokhlin entropy.

In the paper, Corollary 6.1 is derived from Theorem 5.9 (approximately Bernoulli
generating partitions with a prescribed distribution), and Lemma 6.2 by
approximating a relative generating partition by a clopen one. The proofs are not
re-derived here.
