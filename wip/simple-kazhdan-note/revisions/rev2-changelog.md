# Revision 2 changelog (sk-editor-2, 2026-09-13)

- **Base:** main's revision 1 at 5b1890ce6c (md5 8e04b341…, 291 lines). Main may have since landed a one-sentence Origin fix; rev2 uses main's new paragraph verbatim.
- **Output:** `sk/drafts/rev2.tex`, 386 lines, md5 3d6be9dd…, assembled from rev2-partA.tex and rev2-partB.tex.
- **Compile:** MSI, texlive/2025, pdflatex 3 passes in /scratch.global/sauer354/sk/editor2/, md5 checked on both ends. 0 errors, 0 overfull, 0 undefined. 2 underfull hboxes. 5 pages.
- **Name check:** grep for Codex, OpenAI and Astra in rev2.tex finds nothing.

## A. Title, abstract, opening (sk-title-abstract Variant B)
- **Title and pdftitle:** "An infinite simple Kazhdan sofic group" → "Infinite simple Kazhdan groups that are limits of finite simple groups".
- **MSC:** 05C48 added.
- **Abstract:** Variant B verbatim. It names G_X, states the marked limit of SL_{3N}(F_2) with expanders, says LEF, sofic and hyperlinear, answers Brown/Ozawa/Pestov, and says every Turing degree occurs. The order "infinite, finitely generated, simple" now matches the theorem (panel-3 F9).
- **Opening:** O1 verbatim, with one clarification. Before: "Brown asked this in its von Neumann algebra form in 2001 … and Ozawa in the hyperlinear form in 2003". After: Brown's printed question is glossed ("embeddings into unitary groups of McDuff factors that embed in an ultrapower R^ω of the hyperfinite II_1 factor"), "Ozawa stated the hyperlinear form in 2003", and "The groups below answer all three forms positively". The clarification is that R^ω is defined at first use, as `\mathcal R^\omega`, because R names the ring (sk-reader P1 note).
- **Ozawa bibitem:** L1 applied, adding the line "Preprint arXiv:math/0306067 (2003)".

## B. Theorem
- **Added sentence** (Variant B): G_X is the marked limit of finite simple SL_{3N}(F_2) whose Cayley graphs, for the images of a fixed generating set, form expanders; so G_X is LEF, sofic and hyperlinear.
- **EL_n clause:** gains "with SL_{nN}(F_2) in place of SL_{3N}(F_2)".
- **Verification:** see D (Option A) and the two-case check of EL_3(M_N(F_2)) = SL_{3N}(F_2).

## C. Method paragraph (the coordinator's credit order, from sk-panel-referee-1; sk-citations P1)
- **GM credit.** Before: "The finite models use periodic sequences with the same short words as X, as in Grigorchuk and Medynets". After: "The finite models use periodic approximation, as in the proof by Grigorchuk and Medynets that topological full groups of minimal Cantor systems are LEF [GM, Theorem 2.6], and the expanders arise as in Kassabov's construction [Kassabov]."
- **Simplicity credit.** Before: "The new step is simplicity. A nontrivial normal subgroup contains …". After: the coordinator's text verbatim ("Simplicity also follows from Stepanov's theorem on the normal structure of GL_n [Stepanov, Theorem 4.4], since any two elements p,q of the ring satisfy pr+qs=0 with (r,s)≠0, by a dimension count on one cylinder. Our proof is direct: …").
  - The Matui and Thom sentences are unchanged.
  - The "not finitely presented" and "We do not know …" sentences moved to §3 Questions.
- **Stepanov bibitem** kept, now cited for Theorem 4.4. The "level … of N [Stepanov]" citation in the simplicity proof is removed (panel-3 F6; the coordinator's order).

## D. §1 Proof
- **Product rule** (sk-reader P2). The display of the ring now includes "(fu^i)(f'u^j)=f(f'∘T^{-i})u^{i+j}". Checked: u^i f' u^{-i} = f'∘T^{-i}.
- **Generators** (sk-reader P10). "generate G" → "generate G, as 1=Σ_a e_a".
- **Periodic word** (sk-reader P3, panel-3 F4, review 7b.ii). m_ℓ → m (used only to build y_ℓ).
  - The text now says y_ℓ agrees with x on [0,m+2ℓ).
  - Windows starting in [0,m) are words of X, and every word of length 2ℓ+1 starts in [0,m).
  - NEW: N_ℓ is the least period of y_ℓ. Checked: every window of an N-periodic sequence occurs at a position in [0,N), so N_ℓ ≥ #words.
  - The growth claim is "tends to infinity with ℓ, since a subshift with boundedly many words of each length is finite" (7b.ii).
  - The model space is F_2^{Z/N_ℓ}. The least period is needed so that the rotations are distinct and ρ_ℓ is onto; rev1's m_ℓ need not be least. All model identities hold for any period.
- **Domain of φ_ℓ and quantifiers** (sk-reader P11, panel-3 F5). "When every f_j depends only on coordinates in [−ℓ,ℓ], put φ_ℓ(…)"; "for fixed r,s∈R"; and "the terms D_ℓ(f_j)P^j have disjoint supports once N_ℓ>2|j| for all exponents j of r".
- **LEF step** (sk-expanders-limits Option A with review 7b.i–iii). Before (rev1 l.130–134): "For a finite F⊆G and large ℓ, applying φ_ℓ … injective map F→GL_{3m_ℓ}(F_2) … So G is LEF. LEF groups are sofic …". After: the free algebra F=F_2⟨t_+,t_−,t_a⟩; π:F→R and ρ_ℓ:F→M_{N_ℓ}(F_2) are onto. The map is named ρ_ℓ, not ψ, because ψ names the simplicity embedding. Verification:
  - **Onto.** P^iD_ℓ(e_a)P^{−i}δ_t = 1[y_{t−i}=a]δ_t. The product over i∈[0,N_ℓ) with a_i=y_{s−i} is the diagonal unit at s, by distinct rotations (7b.i). With P every matrix unit P^jE_ss follows.
  - **EL_3(M_N(F_2)) = SL_{3N}(F_2).** Between-block transvections are e_pq(E_ab). Within-block ones are commutators through another block. Transvections generate SL, and EL ⊆ SL.
  - **Agreement on words.** A word of length n has entries of degree ≤n in F. For large ℓ, φ_ℓ is multiplicative on the finitely many products involved and φ_ℓ(π(t_±))=P^{±1}, φ_ℓ(π(t_a))=D_ℓ(e_a), so φ_ℓ∘π=ρ_ℓ on these entries. For large ℓ, injectivity of φ_ℓ on the finitely many nonzero entries gives: trivial in G ⇔ trivial in SL_{3N_ℓ}(F_2). This yields marked convergence, and LEF follows.
  - **Expanders.** EL_3(F) has (T) by EJZ (F is finitely generated), and |SL_{3N_ℓ}(F_2)|→∞.
  - **Citations.** Kassabov bibitem added (Crossref-verified by sk-expanders-limits). Pestov locators "Example 4.5 and Theorem 3.3" kept (7b.iii).
- **Operator algebras** (sk-operator-algebras Option B + review 9c.i; referee-2 PASS of `brown-mcduff-witness-for-simple-kazhdan-lef-group` and the Kirchberg import, per the coordinator). The new paragraph after the sofic/hyperlinear sentence says:
  - L(G) ⊂ R^ω [Ozawa, Prop 7.1];
  - G is infinite and simple, so it is ICC and not residually finite (9c.i: the reason now comes before the factorization property);
  - L(G) is a II_1 factor, and L(G)⊗̄R is a McDuff factor embedding in R^ω whose unitary group contains G, which is Brown's formulation;
  - Kirchberg Thm 1.1, so G has no factorization property, and C*(G) fails the LLP [Ozawa, p.527].

  A Kirchberg bibitem was added: Math. Ann. 299 (1994) 551–563, doi 10.1007/BF01459798. The operator-algebra facts are imported as reviewed; no new mathematics.
- **Simplicity:**
  - x → z in the scalar step (sk-reader P12).
  - ε_ab (sk-reader P5): nonzero because h≠I_3 ⇒ V≠∅. The product is displayed as e_{T^aV∩T^{a−b+a'}V}u^{a−b+a'−b'}. Checked: the intersection is T^a(V∩T^{a'−b}V), empty unless a'=b, since |a'−b|≤2w.
  - k∈H (sk-reader P4): the image of ψ is the set of matrices with entries in span ε_ab, closed under products; k=I+ψ(A), k^{−1}=I+ψ(B) ⇒ ψ(A+B+AB)=0 ⇒ (I+A)(I+B)=I, so k is the image of I+A.
  - Level sentence: "the level J … of N [Stepanov]" → "J=…".

## E. §2 Word problems
- **GM credit** moved out of the proof to after the corollary (panel-3 F7).
- **Multiplication in the full shift algebra** (sk-reader P6 + panel-3 F8): "Multiplying out a word in the generators in LC(A^Z,F_2)⋊Z, which maps onto R, gives … each f_j given by a table on the words of some length". Checked: restriction LC(A^Z)→LC(X) is equivariant and onto.
- **Sturmian checks** (sk-reader P7):
  - c(θ)_t=1 iff θ∈[−(t+1)α,−tα) mod 1. Checked: {θ+tα}≥1−α.
  - c(θ)_t=⌊θ+(t+1)α⌋−⌊θ+tα⌋, which telescopes to ⌊θ+nα⌋ for θ∈[0,1).
- **Continued fraction** (sk-reader P8): "since each digit is decided by one strict comparison of this number with a rational computed from the earlier digits". Checked: the digit a_{k+1}∈{1,2} is decided by comparing with [0;a_1,…,a_k,2], and the number is irrational.
- **"There are continuum many degrees"** restored before the invariance clause (review 4.i).

## F. §3 Questions (new, 12 lines; sk-open-5 minimal variant, compressed)
- **Q1:** "A finitely presented LEF group is residually finite [VershikGordon], and the infinite simple group G_X is not, so G_X is not finitely presented (sk-reader P9: the reason is given). Is there a finitely presented infinite simple group with property (T) that is sofic, or at least hyperlinear? A positive answer would also answer Open problem 6.1 of Alekseev and Thom …". The Alekseev–Thom bibitem is from sk-open-5, verified against the arXiv HTML. The rev1 intro sentences are removed.
- **Q3:** the easy direction as one sentence ((X,T) conjugate to (Y,S) or (Y,S^{−1}) ⇒ G_X≅G_Y), then the question on flip conjugacy or strong orbit equivalence [GPS]. The GPS bibitem is Crossref-verified by sk-open-5.
- No Q2 (the Z² SFT question) and no Labbé.

## G. Origin and authorship
- Main's paragraph verbatim (the coordinator's user order): no Codex, OpenAI or Astra anywhere in the tex. "wrote the original manuscript" → "wrote the manuscript".

## H. Not applied, and why
- **RF embedding corollary; §1 replacement** (sk-open-2 v5, Stepanov route as proof); **LEF growth sentence; [[T]]′ sentence; F_q remark:** decision (g).
- **sk-expanders-limits Option C** (explicit Kazhdan constant 1/727): the decision log keeps it in Cairn.
- **sk-open-5 Q2 and Labbé:** decision (d).
- **sk-operator-algebras Option C** (no faithful representation into U(R)): the decision log.
- **Panel-3 title options T1–T3:** main decided Variant B.
- **Panel-3 F1** (the LLP remark in the opening): the LLP consequence appears once, in the operator-algebra paragraph with [Ozawa, p.527]. Putting it in the opening too would duplicate it.
- **Panel-3 B5** unsourced "natural candidates" sentence: not added, as the panel itself recommends.
- **sk-reader Tier-1 P1 variant text:** superseded by Option B.
- **Referee-1 and referee-2 proposals from the frozen-copy era:** superseded in rev1.
- **sk-cut-sentences leftovers** (the l.121 roadmap sentence, "completing the proof", the subsection title "detects"): already gone in rev1.

## I. Open doubts for main
1. **Pestov locators** (Example 4.5, Theorem 3.3) are from arXiv v8. The journal numbering is unchecked.
2. **Metadata not confirmed through Crossref by me:** Matui and GMpres (from rev1); Alekseev–Thom and GPS (taken from sk-open-5, which verified them).
3. **Stepanov sentence.** It asserts the dimension count "on one cylinder" and cites Thm 4.4, per panel-referee-1's page-image reading.
   - sk-stable-rank-a raised one referee point: whether Thm 4.4 at level I=R needs normality of E(3,R) in GL(3,R).
   - It is not re-verified here; I applied the coordinator's order as given.
4. **Page count.** 5 pages against rev1's 4. The additions are Option A (+13), operator algebras (+10), Questions (+12), and bibliography (+25 lines: Alekseev–Thom, GPS, Kassabov, Kirchberg, Ozawa preprint line).
