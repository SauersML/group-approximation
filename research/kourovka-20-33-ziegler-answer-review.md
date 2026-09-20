---
rg: 2
id: kourovka-20-33-ziegler-answer-review
kind: claim
title: Referee review of aae1608cbe (Kourovka 20.33 answered yes by Ziegler's generalized Higman theorem) — PASS; the quoted statements of Scott arXiv:2404.11524v1 match at source (HTML numbering differs), Lemmas 1–2 and both directions of the Theorem check, and no printed answer to 20.33 was found, so it stands as an attribution-grade literature answer credited to Ziegler (1980)
distinct_from:
  kourovka-20-33-higman-relativizes-by-ziegler: that is the lane node under review; this checks its quotations, its deduction and its priority status.
---

**ESTABLISHED (referee bh-ref-e, 2026-09-19; review of the lane node by bh-kourovka-scout, landed in
aae1608cbe).** No priority claimed. Read on 2026-09-19:
- Scott, arXiv:2404.11524v1, in its arXiv HTML rendering;
- the arXiv abstracts of 2404.11524 and 2512.10800;
- web searches for any answer to 20.33.
The Kourovka text was not reread in full; see §1. No code was run.

## 1. The problem text

- The node's quotation of 20.33 agrees word for word with the text indexed from arXiv:1401.0300, including "that
  is, there is a finite generating set relative to which the set of relations is computably enumerable with an X
  oracle" and "Higman's Embedding Theorem says that for computable X, one may take G_X = ℤ".
- The node's statement that v46 (p. 152) lists 20.33 as unsolved with no comment is its own reading at source. I
  did not reopen the full PDF.
- **Minor.** The attribution should read as printed, "(A. Bauer)". The node's "posed by J. Grochow" should be
  checked against the printed line, and dropped if the notebook names only Bauer.

## 2. Scott's statements, checked at source

- **Numbering.** The arXiv HTML numbers results sequentially, while the PDF numbers them by section. The node's
  numbers are the PDF's, so cite both:
  - Definition 5.1.1 = Definition 41;
  - Proposition 5.1.2 = Proposition 42;
  - Theorem 5.1.10 = Theorem 50;
  - Definition 5.2.1 = Definition 51;
  - Theorem 5.2.2 = Theorem 52.
- **Proposition 42**, verbatim: "Y ≤_T X iff Y ⊕ Yᶜ ≤_e X ⊕ Xᶜ. Y is c.e. in X iff Y ≤_e X ⊕ Xᶜ." This matches
  the node's use in both directions.
- **Generator independence**, verbatim: "The enumeration degree of W(G, ḡ) does not depend on the choice ḡ of
  generators of G." This matches.
- **Definition 51**, verbatim: "F = ⟨ḡ, f̄ | W(G) ∪ R(ḡ, f̄)⟩ and ḡ generates G in F". This matches, and it is
  exactly the form Lemma 2 consumes.
- **Theorem 52**, verbatim: "W(G) ≤_e W(H) iff G embeds in a finitely presented extension F of H". It is stated
  for finitely generated G and H, as the node says. Only the forward direction is used, with G = Γ and H = H_S, both
  finitely generated.
- **Not checked at source.** The attribution to Ziegler's Theorem II.3.10 (Word Problems II, 1980), and Ziegler's
  own proof.
- **Theorem 50 ([Zie76])** is used only in a remark.

## 3. The deduction, step by step

**Lemma 1 (`W(H_S) ≡_e S`): correct.**
- The elements `a_n = b^(-n) a b^n` (`n ∈ ℤ`) freely generate `ker(F(a,b) → ℤ)`, which is the normal closure of
  `a`.
- So `⟨a_n : n ∈ S⟩` is free on that sub-basis, and `a_m` lies in it iff `m ∈ S`.
- The relators `[t, a_n]` (`n ∈ S`) make `H_S` the HNN extension of `F(a,b)` along the identity of `A_S`.
- For `m ∉ S`, `t^(-1) a_m^(-1) t a_m` has no pinch, so it is nontrivial by Britton's lemma.
- The reduction `m ↦ [t, a_m]` is computable and many-one, hence an enumeration reduction.
- The converse, enumerating the normal closure from finite pieces of `S`, is a correct enumeration operator.

**`W(G_X) ≤_e S`, and the presentation: correct.**
- Triviality in `H_S * ℤ` is witnessed by finitely many syllable deletions, each needing only positive
  information about `W(H_S)`.
- By Proposition 42, `W(G_X)` is c.e. in `X`.
- The relator set `{[t, a_n] : n ∈ S}` is decidable in `X`, since `S ≡_T X`.
- `G_X` is finitely generated, by `a, b, t, z`.

**Lemma 2: correct.**
- `G_X^{*k} ≅ (H^(1) * ⟨z_1⟩ * ⋯ * ⟨z_k⟩) * (H^(2) * ⋯ * H^(k))`, by associativity and commutativity of free
  products.
- `⟨ḡ | W(H_S)⟩ = H_S` gives `F ≅ (H_S * F(f̄)) / ⟨⟨R⟩⟩`.
- `(A * B) / ⟨⟨R′⟩⟩ ≅ (A / ⟨⟨R′⟩⟩_A) * B`, since both have the same universal property, and a free factor embeds.
- The dummy generator for `k ≥ 1` is harmless.

**The Theorem, direction (⇒): correct.**
- An X-computable presentation makes `W(Γ, ȳ)`, the normal closure of an X-c.e. set, c.e. in `X`.
- So `W(Γ) ≤_e S ≡_e W(H_S)`.
- Theorem 52 then gives `Γ ↪ F` finitely presented over `H_S`, and Lemma 2 gives `F ↪ G_X^{*k} / ⟨⟨R′⟩⟩`.
- The image of the finitely generated `Γ` is a finitely generated subgroup.

**The Theorem, direction (⇐): correct.**
- `W(Q)` is enumerable from `R` together with positive information about `W(G_X)`.
- So `{v : v(u_1, …, u_r) ∈ W(Q)}` is c.e. in `X`, and it is an X-computable presentation of `Γ` in the problem's
  sense.

**Sanity check.** For computable `X`, the class is the recursively presented finitely generated groups, and the
quotients `ℤ^{*k} / ⟨⟨R⟩⟩` are exactly the finitely presented groups. So the statement reduces to Higman's
theorem, as the problem says it should.

## 4. Priority

- Kourovka v46 still lists 20.33 as open, per the node's reading.
- Web searches on 2026-09-19 found no printed answer to 20.33. The terms searched were: Kourovka 20.33, relativized
  Higman, X-computable, Bauer, and enumeration reducibility with Ziegler.
- Neither Scott's paper nor Bridson–Nyberg-Brodda (arXiv:2512.10800, abstract) mentions the Kourovka problem.
- Scott's paper states the key theorem in 2024, and the problem was posed in the 20th issue (2022). So the answer
  is **an attribution-grade literature answer**: the mathematics is Ziegler's 1980 theorem, restated by Scott and
  generalized by Belegradek (1996). The lane's contribution is the explicit `G_X`, the free-product bookkeeping
  (Lemma 2), and the observation that 20.33 is the total-degree case.
- The node already says "no priority is claimed" and "may well be known to experts", which is the right grading.
- Before reporting it to the notebook's editors, someone should read Ziegler's Theorem II.3.10 at source. That is
  the user's decision, not a lane's.

## Verdict

**PASS.**
- The answer to Kourovka 20.33 is yes, and the deduction from Ziegler's theorem, as Scott states it, is correct in
  every step.
- Grade: literature answer, credited to Ziegler (via Scott and Belegradek), with no priority.
- Repairs are cosmetic:
  - cite Scott's HTML numbering alongside the PDF numbering;
  - check the "posed by J. Grochow" attribution against the printed text;
  - mark the Ziegler Theorem II.3.10 citation as not read at source.
