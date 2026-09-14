# sk-draft-general: a candidate paper stated over finitely generated groups (self-assessment)

Lane `sk-draft-general`, SK swarm, 2026-09-13.
- Candidate tex: `sk/drafts/sk-draft-general/sk-draft-general.tex` (scratchpad of the coordinator session), about 505 lines, 6 pages.
- Changelog against main's revision 1 (5b1890ce6c): `sk/drafts/sk-draft-general/changelog.md`.
- Compile on MSI (pdflatex, 3 passes): 0 errors, 0 overfull boxes, 0 undefined references; 2 underfull boxes, in the bibliography only.
- Status: the proposed text is UNREVIEWED as a whole; review is requested in `sk/queue/sk-verify-4.txt`.

## 1. What the draft says
- **Theorem 1.** Let a finitely generated group Γ act freely on an infinite minimal subshift X ⊆ A^Γ with finite models: every finite window F has some finite subshift Y with L_F(Y) = L_F(X). Then for every n ≥ 3, EL_n(LC(X,F_2)⋊Γ) is infinite, finitely generated, simple, Kazhdan and LEF, so it is sofic and hyperlinear. It also carries Brown's McDuff form, no factorization property, and C*(G) without the LLP.
- **Proposition 2.**
  - (a) Every infinite minimal Z-subshift qualifies.
  - (b) A free action with finite models forces Γ to be residually finite.
  - (c) Every infinite f.g. residually finite Γ has such a subshift, a nested-hole Toeplitz point.
- **Corollary 3.** Every f.g. residually finite group is a subgroup of an infinite f.g. simple Kazhdan LEF group. It follows at once from Ore, Proposition 2(c), Theorem 1 and the Whitehead identity in characteristic 2.
- **Corollary 4 (over Z).** WP(G_X) ≡_T L(X); every Turing degree occurs; continuum many pairwise nonisomorphic G_X.
- **Questions.** Q1: an f.p. simple Kazhdan sofic group (Alekseev–Thom 6.1). Q2: is every f.g. LEF group a subgroup of an infinite simple Kazhdan LEF group? Q3: rigidity.

## 2. The strongest claim
Simple Kazhdan LEF groups exist over every residually finite acting group, and only over those for this construction. Every finitely generated residually finite group, e.g. SL_n(Z), surface groups or the Grigorchuk group, lies inside one. This is the Kazhdan counterpart of Kionke–Schesler (J. Comb. Algebra 2024, Thm 1.2), whose envelopes are amenable. The answer to Brown, Ozawa and Pestov is the case Γ = Z, where no hypothesis is needed.

## 3. The weakest points
- **Reliance on unreviewed nodes.** The following rest only on my own checks; I re-derived every step while drafting:
  - Theorem 1 over Γ (`finite-model-subshift-elementary-groups-simple-kazhdan-lef`, queued with sk-referee-1, no verdict on main);
  - Proposition 2(b) (`free-subshift-with-finite-models-forces-rf-group`);
  - Proposition 2(c) (`rf-groups-have-free-minimal-subshifts-with-finite-models`);
  - Corollary 3 (`rf-groups-embed-in-simple-kazhdan-lef-groups` and inputs, queued with sk-verify-3);
  - the operator-algebra sentence (`brown-mcduff-witness-for-simple-kazhdan-lef-group`, queued with sk-referee-2).

  Reviewed inputs used: the Z simplicity text (sk-referee-1 PASS), LEF Replacement B, the word-problem components, and Theorem T / Corollary T for the Toeplitz family (by a different construction).
- **The simplicity and LEF texts over Γ are new wording.** They adapt the reviewed Z texts: word length replaces |j|, and finite subshifts replace periodic orbits. Nonvanishing of φ_Y now uses the compactness fact F_γ, which needs freeness at every point. That is why Proposition 2(c) proves freeness everywhere, not just on a dense orbit.
- **Length.** Six pages against rev1's four. The generality costs Γ-notation in the proof, one proposition (about 50 source lines) and one corollary proof (about 25 lines).
- **Credit gaps:**
  - Kerr–Nowak is cited only as related work. I did not read their definition, so the draft does not claim that finite models are their residually finite actions.
  - Krieger's Toeplitz subshifts over RF groups are not cited, because Crossref did not find the reference.
  - The Kionke–Schesler volume number is missing.

## 4. What a referee will attack
1. **Framing.** The headline question lives over Z. A referee may ask for the Z theorem first and the Γ version as a section. The counterargument: over Z no hypothesis is needed and the statement of Theorem 1 is only one line longer.
2. **Proposition 2(c), minimality.** It uses "almost periodic ⇒ minimal orbit closure" for group actions (Gottschalk), which is standard but uncited.
3. **Corollary 3.** Check the overgroup step (Ore coordinatewise in ∏ Sym, with Δ f.g. RF infinite) and that diag(c,1,1) ∈ EL_3 needs c ∈ [R^×, R^×]. The draft never uses diag(a,a^{-1},1) as a homomorphism.
4. **Novelty of Corollary 3.** The search was bounded: sk-universal-embedding-a's two web queries and sk-questions-ggt's pass. Embeddings into simple Kazhdan groups without approximation properties (Ol'shanskii-type quotients) were not searched in depth.
5. **Locators.** Ozawa Prop. 7.1 and p. 527, and Pestov Example 4.5 / Theorem 3.3, come from arXiv versions. Alekseev–Thom's title comes from the arXiv HTML.

## 5. Comparison with the other architectures
Against rev1 (4 pages), this draft adds the general theorem, the exact residual-finiteness boundary of the method, the embedding corollary, the operator-algebra context, and the questions. None of these changes the Z proof, apart from notation. If main keeps the Z headline, the Γ material can go in as a §2–3 appendix of about 75 source lines, with Theorem 1 restated over Z and a remark "the proof uses only freeness and finite models".

## 6. Firewalls respected
- diag(a,a^{-1},1) is never used as a homomorphism.
- F_2 only; the binary unit trick is not claimed over F_q.
- No claim that n = 2 loses (T).
- No claim of "first finite model SL_15".
