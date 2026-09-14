# sk-draft-rich: the rich candidate paper (2026-09-13)

Lane `sk-draft-rich` (ROSTER-D Family P).
- **Architecture:** Theorem 1, the two strongest corollaries, and a questions paragraph of at most 15 lines.
- **Draft:** `sk/drafts/sk-draft-rich/sk-draft-rich.tex`, 448 lines, md5 6253fccafb3b24a4c7af6e5aaaaa7f17. The halves are `partA.tex` and `partB.tex`.
- **PDF:** `sk/drafts/sk-draft-rich/sk-draft-rich.pdf`, 5 pages.
- **MSI compile** (texlive 2025, pdflatex, 3 passes, `/scratch.global/sauer354/sk/sk-draft-rich/`): 0 errors, 0 overfull boxes, 0 undefined references. Two underfull boxes, one in the Questions list and one in the Kionke–Schesler bibitem, badness about 1100–1400.
- **Base:** main's revision 1, 5b1890ce6c (md5 8e04b341…, 292 lines).

## 1. Changelog against main (revision 1)
1. **Abstract.** Adds "Every finitely generated residually finite group is a subgroup of an infinite simple Kazhdan LEF group". The Turing clause is kept.
2. **Credit paragraph.** GM wording follows sk-citations P1: "periodic approximation, as in the proof by Grigorchuk and Medynets that topological full groups of minimal Cantor systems are LEF [GM, Theorem 2.6]".
3. **Finite-presentation sentences.** They move from the intro into the Questions paragraph (rev2-decisions item 18).
4. **New intro paragraph (7 lines).** It says the proof needs only a free minimal subshift with finite models, which every residually finite group carries, and points to Corollaries 2 and 3.
5. **After "sofic groups are hyperlinear".** sk-operator-algebras Option B (rev2-decisions item 17):
   - L(G) ⊂ R^ω [Ozawa, Prop. 7.1];
   - ICC, so L(G)⊗̄R is a McDuff factor embeddable in R^ω whose unitary group contains G, "as Brown asked";
   - Kirchberg [Thm 1.1]: G lacks the factorization property;
   - C*(G) fails the LLP [Ozawa, p. 527].
6. **New §2 "Residually finite subgroups" (about 60 source lines).** Corollary 2 with a complete proof:
   - (a) The overgroup Γ ≤ [Δ,Δ], via left multiplication on Γ/Γ_n × {1,2} and Ore's Theorem 1.
   - (b) A three-letter array x on Δ: x(1) = 1, and one coset valued 1, one valued 2 and the rest 0 on each K_m∖K_{m+1}, with [K_m:K_{m+1}] ≥ 4. It is proved minimal, free at every point, and to have finite models (p_0, p_1, p_2 constant on K_n).
   - (c) The proof of Theorem 1 over Δ, as a list of substitutions: word length, finite models on ⊕_c F_2^{Δ/K_n}, small sets for B_{2w}, tower units e_{aV}u_{ab^{-1}}, freeness for the scalar step, covering translates.
   - (d) The Whitehead identity over F_2 and diag([a,b],1,1) ∈ EL_3, so γ ↦ diag(u_γ,1,1) embeds Γ.
7. **§3 Word problems.** Revision 1's §2, unchanged, with label `cor:wp`.
8. **New `\section*{Questions}` (14 lines).**
   - An f.p. LEF group is RF, so no G_X is f.p.
   - Q1: an f.p. infinite simple Kazhdan sofic or hyperlinear group (Alekseev–Thom Open problem 6.1).
   - Q2: does every f.g. LEF group embed in an infinite simple Kazhdan LEF group?
   - Q3: does G_X ≅ G_Y give flip conjugacy, or strong orbit equivalence (GPS)? It includes the easy direction.
9. **Bibliography.** Six added: AlekseevThom, CortezPetite (Crossref: J. Lond. Math. Soc. (2) 78 (2008) 1–20, doi 10.1112/jlms/jdn002), GPS, KionkeSchesler, Kirchberg, Ore. Macro `\diag` added.
10. **Unchanged:** the Theorem, the proof of Theorem 1 (except item 5), and the Origin paragraph (main's revision-1 wording).

## 2. Mathematical status
- **Reviewed PASS on main.**
  - All of Theorem 1's proof (sk-review-1 parts 1–3).
  - Corollary 3 (sk-review-2 part 1: continued fractions and the route).
  - `simple-kazhdan-group-lacks-factorization-property` (PASS with repair). Kirchberg's DOI is confirmed via Crossref; only the verified direction (T)+(F) ⇒ RF is used.
- **Unreviewed.**
  - The Brown–McDuff witness sentence (`brown-mcduff-witness-for-simple-kazhdan-lef-group`, queued with sk-referee-2). It uses only standard steps: ICC, McDuff's R⊗̄R ≅ R, and tensor embedding in R^ω.
  - Corollary 2 and its text. Inputs: sk-universal-embedding-a (3bcc003284, queued with sk-verify-3) and sk-general-actions-a's array (e3d0976807, queued with sk-referee-1). The draft's text is queued with sk-verify-4.
- **My own verification of Corollary 2**, every step re-derived:
  - Doubling makes left multiplication even. Ore gives s = [a_s,b_s] inside Δ, so Γ ≤ [Δ,Δ], and Δ ≤ P is residually finite.
  - x(hk) = x(h) for h ∉ K_m and k ∈ K_m.
  - Minimality: a pattern at σ with Fσ ∩ K_m ⊆ {1} recurs on σK_m, or on σ times the 1-coset.
  - Freeness: δ = σ⁻¹γσ ∈ K_m∖K_{m+1}. The 1-coset and the 2-coset meet the transversal Tσ. Right multiplication by δ changes the K_{m+1}-coset, and both images lying in K_{m+1} would force the 1-coset and the 2-coset to coincide.
  - Finite models: FF⁻¹ ∩ K_n = {1} leaves at most one h in K_n. The value c is realized at σk because x takes all three values on K_n.
  - Over Δ, u_g D(f) u_g⁻¹ = D(f∘g⁻¹) with u_gδ_{hK} = δ_{ghK} and Dδ_{hK} = f(h·p_c). Separation uses normality of K_n. The product formula f u_a e_V f′ u_b ∈ {0, e_{aV}u_{ab}}; the matrix units need disjointness up to length 2w.
  - Whitehead over F_2: e_12(c)e_21(c⁻¹)e_12(c)·e_12(1)e_21(1)e_12(1) = diag(c,c⁻¹).
- **Defect found in sk-general-actions-a Tier 2 (fixed in this draft).** With [K_m:K_{m+1}] = 3 there are only two nonidentity cosets per level, so the value 0 never occurs and "takes every value of x on K_n" fails for p_0. The draft requires index ≥ 4. sk-general-actions-a's node `rf-groups-have-free-minimal-subshifts-with-finite-models` should get the same repair; the fix is to take p_c only for values occurring on K_n, or to require index ≥ 4.

## 3. Self-assessment (one page)
**Strongest claim.**
- One note proves three things: an infinite simple Kazhdan group that is LEF (answering Brown 2001 in its printed McDuff form, Ozawa 2003 and Pestov 2008), the Kazhdan counterpart of Kionke–Schesler (every f.g. residually finite group lies in such a group), and continuum many examples realizing every Turing degree.
- The Kirchberg/LLP sentence tells the reader why Ozawa asked, and the questions paragraph poses the next three problems.

**Weakest point.**
- §2's "the proof of Theorem 1 now applies" paragraph is a list of substitutions, not a proof written out over Δ. A careful referee must redo the tower calculus with word length and the finite models on ⊕_c F_2^{Δ/K_n}. It is correct (checked above), but it asks for trust; the price of avoiding it is about 25 more lines.
- sk-draft-general avoids this by stating Theorem 1 over Γ.

**What a referee will attack.**
1. **Length versus "short".** 448 source lines and 5 pages, against revision 1's 292 lines and 4 pages. §2 is about 60 lines. A referee may ask for §2 as a separate remark, or for the general-Γ theorem instead.
2. **Credit for Corollary 2.** Kionke–Schesler Theorem 1.2 (no (T)) is cited by the arXiv number; the journal numbering is unchecked. "Arrays of this kind go back to Toeplitz sequences" credits Cortez–Petite in general terms only. Krieger's Toeplitz paper was not found in Crossref and is not cited.
3. **The Brown sentence.** "as Brown asked" relies on McDuff's theorem without a citation. A referee may want McDuff 1970 or a textbook pointer, and the node is not yet reviewed.
4. **Two independent Ozawa citations** (Prop. 7.1, and the p. 527 remark) are fine, but the journal page for Prop. 7.1 is not given.
5. **Q2 overlaps open lanes.** If sk-lef-embedding-c/d/e or sk-universal-embedding-b settle it, Q2 becomes a theorem or goes.
6. **Compatibility with main's rev2.** Expanders Option A and the plural title "…limits of finite simple groups" are orthogonal to this draft. They slot into the finite-models paragraph and the title, and §2's finite models would then read "the images of EL_3(F_2⟨…⟩)".

**Line budget if main takes pieces separately:**

| Piece | Source lines | Status |
|---|---|---|
| Brown/Kirchberg | +8 | brown-mcduff unreviewed |
| §2 | +60 | unreviewed |
| Questions | +14 | intro loses 4 |
| Intro paragraph | +7 | |
| Bibliography | +31 | |
