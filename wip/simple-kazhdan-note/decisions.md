# Revision 2: main's decisions (applied on top of rev1 once it lands)

Line numbers refer to the frozen disk copy unless stated otherwise. "PASS" means a verifier lane passed it.

## Credit (factual; always apply)
1. **Matui credit, Stepanov sentence out** (sk-novelty P1). The note's simplicity pattern follows Matui 2006 (Thm 4.9 with Lemma 3.4): a commutator with a small-support element lands in simple groups on towers. Stepanov's Lemma 4.3 is not used by the note's proof.
2. **Grigorchuk–Medynets credit at the word-problem step** (sk-novelty P2, J. Algebra 500 (2018), Thm 1.1(3)). Their full group has a decidable word problem iff the language is recursive.
3. **Thom citation** (sk-questions-ggt P1). `\cite[Theorem~1.4]{Thom}` → `\cite{Thom}`. Theorem 1.4 is the no-factorization-property statement; non-residual finiteness is in the abstract and on p. 3.
4. **Caprace–Rémy**, only if cited: sk-citations confirms the theorem numbers for f.p., simple and (T).
5. **Kionke–Schesler**, only if a universal-embedding sentence goes in: they already embed f.g. RF groups in f.g. simple LEF groups without (T).

## Mathematics (apply after review PASS)
6. **Finite models** (sk-expanders-limits Option A). Replace the partial-homomorphism paragraph with: the surjection of the free algebra onto M_N(F_2) makes G_X and SL_{3N}(F_2) quotients of one Kazhdan group EL_3(F). This gives, in one paragraph: marked convergence, LEF, finite simple models, and expanders. Credit Kassabov 2007 (Invent. Math. 170, 297–326). Requires a referee PASS.
7. **F_q remark** (sk-coefficients 4-line version). Include it only if a short correct proof sketch fits: κ is never a nontrivial scalar. Otherwise leave it in Cairn.
8. **Fp sentence** (sk-fp-sofic-a Option B; its Option A had a wording error flagged by sk-verify-3). "A finitely presented LEF group is residually finite, so $G_X$ is not finitely presented. We do not know whether some finitely presented infinite simple Kazhdan group is sofic." This is already in rev1. Also check its position against sk-questions-ggt P2 (Alekseev–Thom Open problem 6.1 asks for f.p. sofic non-RF Kazhdan groups; citing it is optional).
9. **Factorization property** (sk-questions-oa). At most two lines. Decide when rev2 is assembled; the cap is two corollary items (sk-cut-structure C budget).

## Structure (decided)
10. **§2 stays**, with sk-word-problem's text (every Turing degree, WP ≡_T L(X), continuum many pairwise nonisomorphic). The counting variant B′ was rejected: the Turing version is stronger, explicit and new within the search.
11. Apply the sk-cut-sentences leftovers not already in rev1:
    - the l.121 roadmap sentence;
    - the credit merge at l.56–62;
    - "completing the proof";
    - the subsection title.
12. sk-arbitrary and sk-hypotheses-sharp: apply their verified items when they land.

## Simplicity route (decide on the rev2 read-through, after referee verdicts)
13. Compare two simplicity texts:
    - rev1's constant-tower proof: F_2 only; it lands k in one GL_d(F_2) and uses the simplicity of GL_d(F_2);
    - the local-annihilation lemma of sk-general-master (b66676817d) and sk-proof-minimal-conceptual (2acfcb8559), about 49 lines. It covers every finite field and every n ≥ 3, and needs no towers and no simplicity of GL_d(F_2).

    Main's lean: if the local-annihilation text is as short and a referee PASSes it, use it and state the theorem for every F_q and n ≥ 3 modulo the centre, with G_X over F_2 as the main case. That is more general at the same length, with one fewer imported fact.
    Counterweight: the finite-simple-group picture ties simplicity to the finite models.
14. Optional 3-line remark (sk-general-master): EL_n(R)/Z is infinite, simple and Kazhdan for every f.g. simple ring with local annihilation. Include it only if item 13 adopts the lemma.
15. sk-general-actions-b proposes no change for the note. If a generality remark beyond Z goes in, add its two-line limitation: over Z² there are no such models for subshifts of aperiodic tilings.

16. Fibonacci example (sk-open-3 option B, 4 lines, unreviewed): the Fibonacci words f_k give the models, and the r-ball embeds in SL_{3|f_k|}(F_2) once |f_k| ≥ 4r. It is a candidate for the "useful" slot if item 6 does not already make the finite models explicit. Never write "first finite model SL_15": `aba` already models the 2-ball in SL_9(F_2).

17. **DECIDED: operator algebras** (sk-operator-algebras Option B, b01d8ea1f5, after referee-2 PASS). It supersedes item 9. Extend the sofic/hyperlinear sentence with:
    - the Brown bridge: L(G) ⊂ R^ω, so G ⊂ U(L(G)⊗̄R), a separable McDuff factor embeddable in R^ω. This is exactly Brown's printed form, and the note's "answers Brown" claim needs it; R^ω itself is not separable.
    - Kirchberg Thm 1.1 (Math. Ann. 299 (1994) 551–563, doi 10.1007/BF01459798): G has no factorization property.
    - C*(G) fails the LLP [Ozawa, p. 527]. This is Ozawa's reason for asking.

    Cost: +8 text lines, +5 bibliography lines. Leave out the U(R) clause (Option C).
18. **DECIDED: questions paragraph** (sk-open-5, minimal variant, compressed to at most 15 lines). Keep Q1 and Q3:
    - Q1: an f.p. infinite simple Kazhdan sofic or hyperlinear group. Credit Alekseev–Thom Open problem 6.1. The rev1 f.p. sentence moves into this paragraph.
    - Q3: does G_X ≅ G_Y force flip conjugacy or strong orbit equivalence? Drop Q3 if sk-rigidity-* settles it; shrink it to the flip-conjugacy form if they prove strong orbit equivalence.
    - Drop Q2 (Z² SFT) and Labbé.
    - Do not pose "is C*_r(G_X) MF": famous-level, and not needed.

19. **DECIDED: nothing beyond Z in the note by default** (sk-general-actions-a Tier 1 +16, Tier 2 +21). The single exception: if sk-universal-embedding-a lands `rf-groups-embed-in-simple-kazhdan-lef-groups` and a referee PASSes it, consider a corollary "every f.g. residually finite group embeds in an infinite f.g. simple Kazhdan LEF group", credit Kionke–Schesler (without (T)), and budget ≤ 12 lines. Decide on reading its proof.
20. **DECIDED: no hypotheses paragraph** (sk-hypotheses-sharp Option 0). The hypotheses are visibly used. FIREWALL: never write "n = 2 loses (T)"; it is false when X has a finite cyclic factor.
21. **DECIDED: no rigidity text** (sk-rigidity-intrinsic). Q3 in item 18 stays open. Its easy direction (flip conjugacy ⇒ isomorphism) can be a clause inside Q3.

22. **RF embedding corollary: proved by sk-universal-embedding-a** (3bcc003284; proposal 26af488fc6). Every f.g. RF group is a subgroup of an infinite f.g. simple Kazhdan LEF group.
    - Proof: Γ ⊆ [Δ,Δ] by Ore; the envelope EL_3 over a free Toeplitz Δ-subshift; γ ↦ diag(u_γ,1,1).
    - Review: queued with sk-verify-3, priority 1.
    - Main's lean: include it after a PASS, as a compact corollary of at most 20 lines (Version B style). Add one remark that the proof of Theorem 1 uses only a free minimal subshift with finite models, over any f.g. group. Credit Kionke–Schesler 2023 (the version without (T)), Ore 1951, Krieger / Cortez–Petite (Toeplitz).
    - Open follow-up: the LEF version, which would make LEF exactly the f.g. subgroups of such groups. Lanes: sk-universal-embedding-b, sk-lef-embedding-c, sk-lef-embedding-d (launched ~19:15).

23. **FIREWALL for any F_q remark** (sk-referee-1 warning). The binary simplicity texts find the noncommuting root among e_ij(e_V) using LC(X,F_2)^× = {1}. Over F_q a nonconstant unit commutes with every e_ij(e_V). So an F_q remark must not say "with the same proof". Either name the change (roots e_ij(e_C u) are needed, and the scalar case is excluded by the extreme-column argument), or cite the all-q route (short-a part2 §2).
24. **sk-arbitrary items to apply** (9e1ac9503e; queued with sk-referee-1):
    - A2: define E_ab(W) = u^a e_W u^{-b}. It is convention-free, and the product rule and absorption each take one line.
    - A10: "R is simple" is unused; it is already in rev1 through the covering step.
    - A11: notation clashes. w is both the segment and the exponent bound, N both the period and the normal subgroup, k both the window and [g,h]. Rename them.
    - A12: the continued fraction; already in rev1 through sk-word-problem.
    - EL_n for n ≥ 3 at zero cost; already in rev1.
25. **No rigidity text** (sk-rigidity-ring). Theorem R (M_m ring isomorphism ⇒ SOE) and R1 (odd q) stay in Cairn. Q3 in item 18 stays.

26. **Rev1 (sk/drafts/rev1.tex) read through by main and verified step by step.** Main's fixes before landing:
    - the generator 1 dropped;
    - `\cite{Thom}` instead of Theorem 1.4;
    - the Origin paragraph now says "Codex (OpenAI) shortened an earlier version, and Claude revised this one".
27. **§1 candidates for rev2** (decide after the referee-1 verdicts):
    - sk-open-2 v5: a one-page proof, 67 source lines against rev1's ~115. Its finite models come from orbit points recurring at position p, with no periodic-word lemma, and it uses the unit trick and constant towers.
    - sk-stable-rank-b: about a 20-line simplicity section through Stepanov Thm 4.4 condition (b) plus pair dependence in amenable crossed products. It covers all q and n ≥ 3, but the reader must trust Stepanov's theorem, and it conflicts with the Matui "same way" credit sentence.
    - sk-general-master: the local-annihilation lemma.

    Main's lean: sk-open-2 v5 if it PASSes, because it is shortest, self-contained, and keeps the finite-simple-group picture.
28. **Citations to apply** (sk-citations):
    - P1 GM credit wording: the finite models use periodic approximation, as in their proof that topological full groups are LEF [GM, Thm 2.6];
    - P5 Pestov locators: already in rev1;
    - P8 DOIs for any retained bibitems;
    - Ozawa p. 527: keep; unconfirmed against the journal but very likely right.
29. **LEF growth sentence** (sk-lef-growth Option 1, +3 lines): "for the ball of radius r, ℓ = 2r suffices and m_ℓ ≤ 2R whenever every word of length R contains all words of length 4r+1". Candidate for the "useful" slot; apply after review. The Sturmian exp(Θ(r²)) result stays in Cairn.
30. **No note change from these lanes:** sk-characters (partial character rigidity), sk-open-1 (normal subgroups ↔ subsystems), sk-open-4 (the K-theory dictionary), sk-generators (three generators; its P1 is applied).

31. **Rev1 LANDED 5b1890ce6c.** Rev2 starts from that blob (md5 8e04b341…).
32. **Referee point for the Stepanov route** (sk-stable-rank-a). Check that Stepanov Thm 4.4 at level I = R does not use normality of E(3,R) in GL(3,R), which nobody knows for R_X. Until a referee settles this, the Stepanov route does not replace the self-contained proof.
33. **[[T]] ⊂ G_X** (sk-subgroups, d7c85d2079, unreviewed):
    - over F_2 all of [[T]] embeds, via g ↦ diag(w_g, u^{−I(g)}, 1);
    - over any field [[T]]′ embeds, via diag(w_g,1,1).

    A candidate one-sentence contrast (amenable simple [[T]]′ inside Kazhdan simple G_X), at about +6 printed lines with Matui and Juschenko–Monod; fold it into the "consequences" budget cap of two.

34. **Title and abstract** (sk-title-abstract, 9d88f1dcda).
    - Variant B: "Infinite simple Kazhdan groups that are limits of finite simple groups", with the expanders Option A text in the theorem. sk-review-2 part2 reports that Option A passed review after a repair, so item 6 is unblocked.
    - Main's lean: adopt item 6 and Variant B's abstract. For the title, weigh B against a form that keeps the answer visible, e.g. "Sofic simple Kazhdan groups as limits of finite simple groups". Decide on the rev2 read-through.
    - Always apply: the opening gloss of Brown's printed question, "Ozawa stated the hyperlinear form", and the Ozawa preprint line (2003) in the bibitem.

35. **sk-referee-2 verdicts** (parts 1–4, no failures). Repairs sent to sk-editor-2:
    - Option B: "not residually finite" comes before "no factorization property"; credit Ozawa's p. 26 / p. 527 remark.
    - Option A: P generates all matrix units; N → ∞; Pestov locators pinned.
    - Rev1 word problems: restore "there are continuum many degrees".

36. **USER ORDER: no OpenAI, Codex or Astra in the note.** The Origin fix landed on main at 2050a8eed1 (blob md5 65d47cb4…, pdflatex clean). Rev2 must use that paragraph; sk-editor-2 was told.
37. **RF embedding corollary: double PASS** (sk-verify-3 part3 + sk-verify-4 part1, a7458be361). Theorem G, the free minimal subshift with finite models over any f.g. group, also PASSes. So it can go in rev3. Credit Kionke–Schesler (the version without (T)).
38. **LEF iff theorem** (sk-universal-embedding-b, 22e2749154, unreviewed): a f.g. group is LEF iff it is a subgroup of an infinite f.g. simple Kazhdan LEF group. If it passes (sk-verify-3, sk-verify-4, sk-lef-embedding-c adversarial), it supersedes item 37 as the corollary.
    - Host: L = Z/2≀Δ on 2^Δ.
    - Shortest note text: sk-lef-embedding-e (target ≤ 20 lines).
    - Open: sk-lef-embedding-d on whether the Z-family G_X is itself universal.
39. **sk-reader Tier 1 for rev3**, unless sk-editor-2 already applied them:
    - P1 Brown bridge (= item 17);
    - P2 display the product rule (fu^i)(f′u^j) = f(f′∘T^{-i})u^{i+j};
    - P3 y_ℓ agrees with x on [0, m_ℓ+2ℓ) and every window starts in [0,m_ℓ);
    - P4 why k ∈ H: k = I+ψ(A), k^{-1} = I+ψ(B), (I+A)(I+B) = I;
    - P7 the Sturmian telescoping count.

    Tier 2: P5 (V ≠ ∅), P9, P10 ("as 1 = Σ e_a"), P12 (rename the reused x).

40. **sk-referee-1 final** (parts 1–11, 34 entries, no GAP or FAIL).
    - PASS:
      - sk-open-2 v5 one-page §1 (67 source lines);
      - sk-proof-minimal-concrete v2, tower-free (−56 lines);
      - the conceptual two-lemma version;
      - the explicit-extraction route;
      - the ideal/sandwich classification;
      - the sharp-hypothesis nodes;
      - sk-arbitrary A1–A14, sk-cut-sentences M1–M5.
    - CONDITIONAL: the Stepanov routes. Their quotation of Thm 4.4 (p. 2152) was not re-read. Do not cite Stepanov Thm 4.4 until someone reads that page.
    - DECISION for rev3 §1: compare sk-open-2 v5 (67 lines) with rev1's §1 on the rev3 read-through. Adopt v5 if it reads at least as clearly: fewer lines, and the same finite-simple-group picture. Its finite models come from orbit points recurring at position p, which removes the periodic-word lemma.
    - Carry-over notes: define EL_3 and state uniqueness of coefficients (rev1 does both); rename the reused letters c/d in v5.

41. **Panel referees, phase 1** (-2 e56b091582, -3 270d116a2e). Main's DECISIONS for rev2/rev3:
    - B1 (MUST): the Brown bridge + Kirchberg + LLP; already in rev2. Optional clause via Kirchberg Cor 1.2: G_X does not embed in U(R) itself. ADOPT: one clause.
    - B2: delete "The new step is simplicity." The novelty is the group: the first infinite simple Kazhdan group shown to be LEF. Keep the Matui credit for the localization pattern. Do NOT add a Stepanov Thm 4.4 sentence until its p. 2152 quotation and the E(3,R)-normality point (item 32) are verified.
    - B3: remove `~\cite{Stepanov}` from the "level" sentence (standard term) and drop the bibitem if unused; add the arXiv:math/0306067 (2003) line to the Ozawa bibitem.
    - B5: the opening gains Ozawa's LLP remark as the reason the question matters (panel-3 F1).
    - Structure for rev3 (panel-3 §3): intro, §1 proof, §2 residually finite subgroups (item 37, double PASS; the LEF iff version if it passes), §3 word problems, §4 questions (≤15 lines). The abstract mentions the embedding corollary.
    - Title: rev2 uses sk-title-abstract Variant B ("... limits of finite simple groups"). Panel-3 prefers T1, "Sofic infinite simple groups with property (T)". Decide at rev3 from the phase-2 draft rankings. Main's lean is B, because it states a stronger property.
42. **sk-draft-minimal**: 3 pages, 288 lines (31b5ccbce8). It adds ε_ab = u^a e_V u^{-b} and removes the level ideal and Stepanov in favour of two commutators plus covering. It is the short end; compare it against rev2/rev3 when the panel ranks.
43. **sk-open-6**: the sequence formulation. G_x = EL_3 of the operator ring generated by σ^{±1} and letter multiplications on F_2[Z], so no subshifts, compactness or crossed products are needed to read the paper (−17 lines; unreviewed, queued with referee-1). A rev3 candidate for the statement plus a remark; decide on readability once reviewed.

44. **Stepanov credit (supersedes item 41 B2's "do not add").** sk-panel-referee-1 read Stepanov Thm 4.4 from the page images. For a simple ring only I = 0 matters, so the normality concern in item 32 does not arise. Condition (b) is the pair-dependence count, derived independently by sk-stable-rank-a and sk-stable-rank-b and re-derived by panel-1. Rev2 uses panel-1's sentence: "Simplicity also follows from Stepanov's theorem ... Our proof is direct: ...". The level citation is removed and the bibitem kept; sk-editor-2 was told.
45. **The four drafts are done:**
    - minimal: 3 pp, 288 lines;
    - rich: 5 pp, 448 lines. It adds §2 (the RF embedding, about 60 lines), OA Option B and a questions paragraph. It found the index-3 defect in sk-general-actions-a's array node, queued with sk-verify-4;
    - ring: 4 pp, 352 lines; not recommended by its author;
    - general: 6 pp; Γ headline with Prop 2 and Cor 3.

    Architecture for rev3: panel phase 2 ranks the drafts. Main's lean is the rev2 base plus §2 from sk-draft-rich (RF embedding, or LEF iff if it passes), with the proof of Theorem 1 kept over Z and a short "any f.g. group acting freely with finite models" remark. The general draft's 6 pages is too long.

46. **LEF iff theorem: first PASS** (sk-verify-3 part6, 8cd576c2be). A f.g. group is LEF iff it is a subgroup of an infinite f.g. simple Kazhdan LEF group. Still pending: sk-verify-4 (queue) and sk-lef-embedding-c (adversarial).
    - CAVEAT: the lamplighter action Z/2≀Δ on 2^Δ is only topologically free, so rev1's tower proof does not apply as written. Its simplicity rests on the repo's local-annihilation / Steinberg criterion, which is unpublished.
    - Rev3 architecture options:
      - (i) rev2 + §2 "LEF groups" with a density patch that makes the tower proof work for topologically free minimal actions (sk-lef-embedding-e is writing the shortest text);
      - (ii) the ring headline (sk-draft-ring's local-annihilation lemma) with dynamics corollaries: subshift groups, LEF iff, Turing.
    - Decide on the patch's length and the panel's phase-2 ranking. Lean: (i), if the patch is ≤ 8 lines.
    - The abstract should then say: "a finitely generated group is LEF if and only if it is a subgroup of an infinite simple Kazhdan LEF group".
47. **sk-verify-5 notes on Option B** (apply on the rev2 read-through):
    - N1: Ozawa Prop 7.1 numbering is checked in arXiv only. Cite as "[Ozawa, Proposition 7.1]" with the arXiv line in the bibitem.
    - N2: "not residually finite" comes first (sent).
    - N3: make the chain explicit: ICC ⇒ L(G) is a II_1 factor ⇒ L(G)⊗̄R is McDuff.
    - Also: the index-node repair (finite orbits), and four sharp-hypothesis claims PASS.

48. **Universal host U′** (sk-strong-3, f222686f87, unreviewed; queued with sk-verify-4). One infinite f.g. simple Kazhdan LEF group contains every f.g. linear group, every f.p. RF group and SL_n(Z) for all n.
    - Proof: Wilson 1980 Thm A (countable RF ⇒ 2-generator RF; verbatim from the PDF), plus the RF embedding (double PASS).
    - For rev3 after a PASS: +10 text lines, +4 bibliography lines, right after the embedding corollary. Candidate abstract sentence: "One simple Kazhdan LEF group contains every finitely generated linear group."
    - Main's lean: ADOPT. It is the single most memorable sentence for non-specialists, at a small cost.

49. **REV2 LANDED e80dcf20ad** (md5 4ad49212…). The local checkout's note file was updated to rev2 (md5-guarded). Scratchpad deliverables are landing under wip/simple-kazhdan-note/.
50. **REV3 decided and launched** (sk-editor-3):
    - §2 "LEF groups": the LEF iff theorem (two PASSes: sk-verify-3 part6, sk-lef-embedding-c), based on sk-lef-embedding-e's 31-line text. The density patch makes Theorem 1's proof run for minimal topologically free actions.
    - A universal host paragraph (Wilson), dropped if sk-verify-4 FAILs it.
    - An abstract sentence, and Questions updated.
    - Suspected FALSE node `double-swap-embeds-group-in-derived-subgroup` (sk-sofic-embedding-b): γ ↦ (γ,γ^{-1}) is not a homomorphism; sent to sk-verify-4 as priority 1.
51. **No note change from:** sk-cstar-mf (strong-convergence firewall through SL_{3k}(F_q[t^{±1}]) ⊂ G_X), sk-fp-sofic-d (gluing-developments firewall), sk-rigidity-f2 (root-preserving isomorphisms ⇒ ring isomorphism over F_2; standardness still open), sk-sofic-embedding-b (linear-sofic amenable envelopes).

52. **Wave 8 launched** (ROSTER-F.md, 25 forks): literature and credit, stronger results, simpler text, paper-level lanes.
53. **sk-el2** (3e5a0ff303, unreviewed): EL_2(LC(X,F_2)⋊Z) is infinite, f.g., simple, Kazhdan and LEF for every infinite minimal subshift, via complementary full idempotents plus the EJZK A_2-grading. REV4 candidate: "for every n ≥ 2" in the theorem plus a short rank-two subsection (+33 lines, EJZK bibitem), after review. The expander clause stays n ≥ 3.
54. **sk-panel-referee-2 part2**: rev2 stands; the Stepanov application checked. Apply in rev3: `\cite[Theorem~1.1]{EJZ}` at the expanders sentence, and MSC 46L10.
55. **No note change:** sk-rigidity-cartan (Cartan uniqueness reduced to groupoid-model rigidity; ring isomorphism preserves the SOE class and the complexity growth class), sk-hyperlinear-boundary-b (the von Neumann side has no shortcut), sk-k2-subsystems (the normal subgroup dictionary for finite limit types), sk-wp-embedding (solvable WP hosts for perfect ERF groups).

56. **sk-verify-4 parts 2–4** (~19:55). All rev3 mathematical inputs now PASS:
    - LEF iff (lamplighter host + Corollary 6): PASS, the third independent review after sk-verify-3 and sk-lef-embedding-c.
    - Density patch `tower-simplicity-holds-for-topologically-free-actions`: PASS with a scope repair (f.g. only for expansive actions, i.e. subshifts). Also PASS: sk-strong-4's two equivalences.
    - Universal host (sk-strong-1/3, Wilson route): PASS. There are duplicate Wilson import nodes for sk-cairn-steward to merge.
    - `double-swap-embeds-group-in-derived-subgroup`: FAIL (nonabelian Γ). Demotion in progress; its consumer `amenable-groups-embed-in-simple-kazhdan-linear-sofic` loses its route.
    - Toeplitz index defect: confirmed in the summary sentence only; repaired to index ≥ 4.

57. **sk-panel-referee-4 (dynamics), 123fe1e35a.** Sent to sk-editor-3 for rev3:
    - B1: cite Morse–Hedlund 1938 for "boundedly many words ⇒ finite".
    - B2: every word of X occurs in x_{[0,∞)}.
    - B3: Q3 mentions the Giordano–Putnam–Skau 1999 / Bezuglyi–Medynets 2008 converse for topological full groups.
    - C1: Hedlund 1944; wording fixes.
    - Also panel-2's EJZ locator and MSC 46L10.

    Optional A2, [[T]]′ ⊂ G_X via diag(w_g,1,1), reviewed PASS by referee-2 part3: +4 text and +5 bibliography lines. Decide on the rev3 read-through; main's lean is ADOPT as one sentence in the intro, if the budget allows.

58. **REV2 GAP** (sk-panel-referee-5 B1): e_ij(t) for the free-algebra generators do not generate EL_3(F), because constants are missing, so the expanders sentence is unsupported as written. Fix in rev3: add e_ij(1) to the generators; in the quotients e_ij(1) = ∏ e_ij(e_a).
    - Also sent to sk-editor-3:
      - Margulis credit; Caprace–Rémy existence in Q1;
      - F4 (solvable WP iff L(X) recursive) and B4 (Sturmian clauses);
      - sk-verify-7 W1–W5;
      - sk-simpler-notation N1, N2, N4, N7–N11. N9 moves the OA paragraph after the simplicity proof.
    - sk-verify-6: the Kirchberg/Ozawa/Pestov/Brown citations PASS against primary sources; only the journal pages are unseen.
    - No note change from sk-labbe-matricial (thin-cylinder firewall).

59. **Credit and background batch sent to sk-editor-3** (user order: "all credit and background lit properly attributed and mentioned").
    - sk-lit-credit-audit (98e268fe22), P1–P7:
      - Kazhdan 1967;
      - Rădulescu ("hyperlinear"); Gromov / Weiss (sofic);
      - Elek–Szabó Thm 2;
      - Grigorchuk 1985 / Champetier 2000 (marked groups);
      - Margulis 1973;
      - McDuff 1970;
      - Hedlund 1944 + Lothaire ch. 2.

      Cost: about +4 text lines, +45 bibliography lines.
    - sk-lit-novelty-2 (da70113d45):
      - a 4-line §2 opening (Gorjuškin 1974, Schupp 1976, Kionke–Schesler Thm 1.2, then "adds property (T), applies to every LEF group");
      - the Wilson credit clause;
      - no "first" wordings.
    - All three rev3 results are new within the bounded search. Residual risk R1: the Ol'shanskii–Osin small-cancellation embeddings into simple Kazhdan groups, not read.

60. **Universal LEF host** (sk-universal-lef-host-b, a303f6663a, unreviewed; queued with sk-verify-7).
    - Lemma A: every countable LEF group embeds in a 2-generated LEF group (ultraproduct of symmetric groups, Ore data, isolation words).
    - Theorem B: a countable group is LEF iff it is a subgroup of an infinite f.g. simple Kazhdan LEF group.
    - Theorem C: one such host contains every recursively presented f.g. LEF group, in particular every f.p. RF group, every f.g. linear group, and every G_Y with recursive language.
    - Proposition D: no countable group contains every G_X.
    - DECISION for rev4, after a PASS: replace rev3's Wilson universal-host paragraph with Theorem C (about +20 net lines; no Wilson import; strictly stronger). Theorem B upgrades §2's statement from f.g. to countable groups at no extra cost.

61. **sk-lit-background** (98d07f2f07, 1db46142dd, proposal e8715ae5de). Apply in rev3's read-through or in rev4:
    - BG1 (+4 text, +8 bibliography lines): "Infinite simple Kazhdan groups arise as quotients of hyperbolic Kazhdan groups [Gromov] and as Kac–Moody lattices, which gave the first finitely presented examples [Caprace–Rémy], but none was known to be hyperlinear [Ozawa, Pestov]." The Thom sentence becomes "... not residually finite and so lacks the factorization property [Thom], but his example is not simple."
    - BG2: `\cite{Kirchberg,Radulescu}, \cite[Proposition~7.1]{Ozawa}` for hyperlinear ⟺ L(G) ⊂ R^ω, with Rădulescu cited without a locator.
    - DO NOT PRINT: "Caprace–Rémy gave the first finitely GENERATED simple Kazhdan groups"; "every hyperbolic group surjects onto a Tarski monster".
    - Verified bibitems for about 50 references are in part1.

62. **sk-wp-host** (39a1b8550b, unreviewed; queued with sk-verify-7).
    - Theorem A: no f.g. group with solvable word problem contains every f.p. RF group (via the reviewed KMS-hardness node).
    - Theorem B: a LEF host with recursively bounded LEF growth misses some f.p. RF group (KMS Thm 4.19 depth).
    - So universal hosts (item 60) necessarily have unsolvable word problem and non-recursive LEF growth. Every Sturmian G_X misses some f.p. RF group.
    - For rev4, only with item 60's host: an optional one-sentence sharpness clause, "such a host has unsolvable word problem [KMS]". Main's lean: ADOPT if item 60 goes in; it makes the countability and complexity limits visible.

63. **sk-simpler-onepage** (1cc9b24d1f, unreviewed; queued with sk-verify-7). Candidate §1 on the rev3 parts: 163 → 140 source lines, same proof, compile clean (6 pp).
    - Changes:
      - seam condition x_{[p−ℓ,p+ℓ]} = x_{[−ℓ,ℓ]};
      - H = (1−e)I_3 + GL_3(A) with A = span ε_ab ≅ M_{2w+1}(F_2), which replaces ψ;
      - the OA paragraph moved after simplicity;
      - shorter prose.
    - Kept: small sets, the density patch, least period.
    - Rejected: the partition h-step (needs freeness), omitting expanders, sk-open-6's sequence-language proof.
    - DECISION for rev4 after a PASS: adopt the candidate §1 if its compile holds on the final rev3 base. Optional: sk-open-6's 3-line remark that R is an operator ring on F_2[Z].
    - Warning: `sk/drafts/rev3.tex` (19:55) is stale against the parts, so rev3 must be re-assembled from partA/B/C before it lands.

64. **sk-strong-8** (7e6f60b572, unreviewed; queued with sk-verify-7). A f.g. group is LEF iff it is a subgroup of an infinite f.g. simple Kazhdan group that is a marked limit of finite simple SL_N(F_2) whose Cayley graphs form expanders.
    - The lamplighter host gets surjective "view models" on F_2^{Q_n}: conjugating one coordinate indicator gives all diagonal units, and the flip conjugates give translations, so the models map onto M_{2^{|Q_n|}}(F_2).
    - So §2's hosts have the title's property, and so does the universal host.
    - DECISION for rev4 after a PASS: adopt (+9 lines, no new references). The abstract then reads: "a finitely generated group is LEF if and only if it is a subgroup of an infinite simple Kazhdan group that is a limit of finite simple groups". That is the unified headline, and it matches the title.

65. **DECIDED: typesetting at rev3 landing** (sk-typesetting, 067c1208f9, bf695e78ca). After rev3 is re-assembled and both referees report, run `perl sk/lanes/sk-typesetting/patch3.pl < rev3.tex | perl sk/lanes/sk-typesetting/order.pl > rev3-typeset.tex` and compile once.
    - The patches:
      - P1: `\arxiv` macro, so arXiv ids can break (removes both underfull boxes);
      - P2: Ozawa bibitem order;
      - P3: MSC 22D55 in place of 22D10, add 46L10;
      - P4, P5: keywords and pdfkeywords;
      - P6: `\qed`;
      - P7: `\section*` for Origin;
      - P9: AMS abbreviation for Stepanov;
      - P10: a truly alphabetical bibliography.
    - Also: Kionke–Schesler journal data (J. Comb. Algebra 2024, doi 10.4171/jca/103), per sk-rev3-referee-b.

66. **sk-verify-6 part2** (0a08547105): PASS for the credit-audit P1–P7, novelty-2 and intro-writer texts.
    - One data fix: the Margulis bibitem title must read "Explicit construction of a concentrator" (zbMATH record).
    - Closed: Murray–von Neumann pp. 716–808; Hedlund 1944 pp. 605–620.
    - Precision option from intro-writer: Pestov–Kwiatkowska printed "finitely generated simple Kazhdan groups".
    - Still open for sk-lit-locators: Rădulescu volume/series, Lothaire series number, Milnor locator, Kionke–Schesler volume/pages.

67. **sk-verify-7 part2** (5e3c6359ef).
    - rev3 §2 LEF iff: PASS. Apply at landing:
      - W6: generating R as a ring needs the units u_s^{±1};
      - W7: add the substitution "B_w for {|a| ≤ w}, so d = 3|B_w|" to the "applies word for word" rule.
    - sk-simpler-onepage §1: PASS, with notes to apply if adopted in rev4:
      - N1: end the proof after the level ideal, and make Brown's formulation a remark;
      - N2: seam position m, not p;
      - N3: yy′ = y′y = eI₃;
      - N5: merge the 20:00 credit additions.
    - Universal host: concurring PASS.
    - sk-strong-5: no shorter family. Its second witness G_CAR = EL_3((⊗_Z M_2(F_2))⋊Z) is a marked limit of SL_{3·2^N}(F_2). Firewall: SL_3(Z) is a (T) marked limit of finite simple groups and is not simple. No note change.

68. **sk-strong-6** (9d6965a225) independently reached item 64's theorem, `lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple`, via configuration-space models on 2^{Q_n}. That makes two independent derivations; still unreviewed and queued with sk-verify-7.
    - Table of approximation classes:
      - RF, amenable, residually amenable and residually solvable classes contain no infinite simple Kazhdan group, so their envelope theorems fail.
      - Sofic, hyperlinear, weakly sofic, linear sofic, initially subamenable and operator-MF envelope theorems would each force a non-LEF simple Kazhdan host (the Abels–Prüfer witness).
    - For rev4: take the shorter of the sk-strong-8 and sk-strong-6 texts. Optional one sentence: "LEF is the only standard approximation class with this characterization known; residually finite and amenable classes admit none."

69. **sk-intro-writer** (f93513e516): a one-page introduction replacing rev2 l.40–79. It consolidates:
    - Brown's printed question plus Ozawa's LLP remark;
    - Rădulescu, Gromov and Weiss;
    - the earlier simple Kazhdan groups (Gromov 1987, Caprace–Rémy "first finitely presented");
    - Thom;
    - Pestov–Kwiatkowska's open-status sentence;
    - the results in words, with the Kionke–Schesler credit;
    - the method with the amenable-contrast sentence (Matui, Juschenko–Monod).

    Cost: +27 text lines, +45 bibliography lines; compiles clean; 0.87 page. The universal-host clause is gated on review, and Variant II exists if there is no §2.
    - DECISION: adopt in rev4, merged with BG1/BG2 and with item 64's unified headline if it passes.

70. **sk-verify-4 final** (parts 1–5; 3ab1bef47b): 26 items, one FAIL (double swap, demoted and wired), the rest PASS.
    - REV4 NOW UNBLOCKED:
      - EL_2 PASS: EL_2(LC(X,F_2)⋊Z) is simple Kazhdan LEF, so the theorem holds for every n ≥ 2 (item 53: +33 lines, EJZK bibitem; the expander clause stays n ≥ 3);
      - the RF and LEF embeddings, the universal host, the density patch, not-uniformly-simple.
    - Repairs merged: the index ≥ 4 Toeplitz array; the finite-Γ envelope case; the WP-degree justification (commutation with generators); f.g. only when R is.
    - Keep one canonical Wilson import pair (sk-cairn-steward).

71. **REV4 ARCHITECTURE (main's plan, after rev3 lands):**
    - (a) **Theorem 2**, the general engine (sk-simpler-unify, b64ae5d7fb, unreviewed). A f.g. group L acting minimally and topologically freely on a Cantor set, with R = LC⋊L f.g. and matricial, has EL_n(R) infinite, f.g., simple, LEF and Kazhdan.
      - One complete proof replaces rev3's "applies word for word" substitution list, which a referee would attack.
      - Cost: +14 lines, or about +9 with the statement at the head of §1.
      - Z-subshifts become §2; the lamplighter host follows immediately.
    - (b) §1 text from sk-simpler-onepage (PASS; notes N1–N5), adapted to Theorem 2's word-length notation.
    - (c) The corollary as the unified headline: LEF iff subgroup of an infinite simple Kazhdan marked limit of finite simple expanders (items 64 and 68, after a PASS).
    - (d) Universal host: sk-universal-lef-host-b Theorem C, plus sk-universal-lef-host-a's A1 iff sentence ("a set of f.g. groups lies in one host iff LEF and countably many types"). A2 drops the quotient-doubling overgroup via commutator words (−6 lines). Add the no-decidable-host clause (item 62).
    - (e) n ≥ 2 (EL_2, PASS).
    - (f) Intro from sk-intro-writer with BG1/BG2 and the credit batch.
    - (g) Questions Q1 and Q3.
    - (h) The typesetting patch.
    - Optional: rank-3 converse sentence (sk-rank3-lef-converse, 95cd5d55a7): for countable simple rings with 2×2 matrix units, one LEF EL_n (n ≥ 2) forces exact matriciality.
    - Budget: at most 7 pages.

72. **REV3 assembled** (sk-editor-3; 614 lines, 7 pp, md5 2a0264d7…). Main read it fully and verified it: the density-patch h-step, the e_ij(1) fix, and §2 (doubled regular actions + Ore, minimality and topological freeness, affine models, injectivity from simplicity, the Whitehead identities).
    - Main's edits: W6 (u_s^{±1}), W7 (B_w, d = 3|B_w|).
    - Then: typesetting patch, compile, land after the two rev3 referee reports.
73. **Character rigidity** (sk-characters-rigidity-b, d78467369d, unreviewed; queued with sk-verify-7). Every character of EL_n(LC(X,F_2)⋊Z), n ≥ 3, is c·1 + (1−c)δ_e.
    - Proof: tower groups; two points generate; Larsen–Tiep bounds; a Bessel step.
    - Consequences: L(G_X) is the only II_1 factor representation; the invariant random subgroups are trivial.
    - REV4 candidate after a PASS: a "Characters" subsection (+45 lines, Larsen–Tiep bibitem). High impact for operator algebraists; weigh it against the 7-page budget.
74. **sk-el2-fq** (fa92d5adcb, unreviewed): EL_2(LC(X,F_q)⋊Z)/Z is infinite, f.g., simple, Kazhdan and LEF for every q. REV4 option R3: an "Other finite fields" paragraph (+12 lines) naming the changes (roots e_ij(e_V u), tower margin, SL_d quasisimple, Peirce level step), per item 23.

75. **REV3 LANDED 9047d0d3c9** (~20:45; 618 lines, 7 pp, md5 274f1936…, pdflatex clean after the typesetting patch). Local copy updated. Referee reports a/b still owed; their findings go to rev4.
76. **sk-lit-locators** (0ce25f499d). Locators checked against the journals: EJZ, Kirchberg, Stepanov, Pestov BSL, GM, Kassabov, Thom, Wilson; Ozawa p. 527 and Prop 7.1 confirmed through printed citations. Apply in rev4:
    - GPS pages 51–111 (not 112);
    - Kionke–Schesler "online first (2024)";
    - Stepin credit: `\cite{Stepin,VershikGordon}` for "a f.p. LEF group is residually finite", with a Stepin bibitem;
    - never build on Kirchberg Cor 1.2 item (v), which Thom corrected.
77. **REV4 editor launched** (sk-editor-4) on the item 71 plan. It uses only PASSed inputs; items gated on sk-verify-8 go in once they PASS.

78. **sk-sl3z-bandwidth** (68539769be, unreviewed; queued with sk-verify-7).
    - Theorem: GL_m(LC(X,F_q)⋊Z) has no distorted infinite-order elements; the stable length is at least 1/(2wm), by a Krylov dimension count.
    - Corollary: H_3(Z), SL_n(Z) for n ≥ 3, and BS(1,2) lie in no G_X. The Z-family is NOT universal for LEF groups (refutes `every-lef-group-embeds-in-a-z-subshift-elementary-group`).
    - REV4 candidate after a PASS: the 6-line trimmed paragraph after Corollary 2, explaining why the lamplighter hosts are necessary. A sharp boundary at small cost; credit Cyr–Franks–Kra–Petite as the nearest prior. Main's lean: ADOPT (trimmed).

79. **Rev3 referee reports (on the landed text 9047d0d3c9).** Correctness: sk-rev3-referee-a, 45161f4f98. Credit and exposition: sk-rev3-referee-b, da7a808e92. Neither found an ERROR, and every claim of the abstract and Theorem 1 is proved or correctly cited. Decisions sent to sk-editor-4 for rev4:
    - MUST:
      - a-U9: "A sofic example would also answer Open problem 6.1". A hyperlinear nonsofic example would not.
      - b-B2 = a-U8: `\cite{Malcev}` plus the countability reason (GL_n over a f.g. field). zbMATH confirms Mat. Sb. N.S. 8(50), 1940, Zbl 0025.00804; the pages 405–422 are recalled.
      - b-B1: "the ring is simple~\cite[Corollary~4.6]{ClarkEdie}". Crossref confirms Algebr. Represent. Theory 18(4) (2015) 907–916, doi 10.1007/s10468-015-9522-2.
    - ADOPT:
      - a-U1: the covariance radius (f of radius ≤ ℓ−1);
      - a-U2 = b-U1: uniform quantifiers in the marked limit;
      - a-U3 = b-U6: "the lamplighter group F_2≀Δ acting on F_2^Δ"; only the simplicity proof transfers;
      - a-U7: display the §2 covariance identity;
      - b-U3: Fibonacci = X_{(3−√5)/2};
      - b-D1–D3;
      - b-C6: the published Rădulescu volume;
      - b-C5: the Boone–Higman parallel (≤ 2 lines).
    - CONDITIONAL:
      - a-U4 = b-U4 renames (R_Δ, G_Δ, Ω, σ_n, ξ, Π, ω) and b-U2 = a-U6′: moot if Theorem 2 (item 71a) replaces the substitution list;
      - C4 (Camm) only if checked at source;
      - S1 (every recursively presented RF group) is superseded by item 71(d) if it PASSes.
    - VERIFIED by referee (b): Caprace–Rémy's existence sentence ("infinitely many isomorphism classes of finitely presented infinite simple groups with Kazhdan's property (T)", via Dymara–Januszkiewicz) is correctly credited.
    - NEW QUESTION for rev4 (≤ 2 lines, no partial result claimed): is every sofic group a subgroup of an infinite finitely generated simple Kazhdan sofic group? This is the sofic analogue of Corollary 2.
80. **sk-matricial-stability** (cc3d14e230, unreviewed; queued with sk-verify-7).
    - For n ≥ 3, every finite-dimensional unitary representation of SL_n(F_q[t^{±1}]) has finite image; for n ≥ 4 it has vectors invariant under the block SL_2, so the group is not purely matricial field.
    - If SL_4(F_q[t^{±1}]) is point-norm matricially stable, then C*_r(Γ) is not MF for every countable Γ containing it, including every G_X.
    - Stability itself is OPEN (the corona full-spectrum case). No note change (decision 18).
81. **sk-measured-subshift** (db789b76bb, 38c836f9a6, unreviewed; queued with sk-verify-7).
    - LC(2^Δ,k)⋊(Z/2≀Δ) has faithful rank models for every f.g. infinite sofic Δ (Bernoulli counting over colorings of sofic approximations).
    - So every f.g. sofic group is a subgroup of an infinite f.g. simple Kazhdan F_2-linear-sofic group.
    - The measured free minimal subshift question stays open (Kerr–Li, Bernshteyn and Elek 2021 read at source).
    - No note change: linear soficity answers no printed question here. The note gets the sofic-host question of item 79.
82. **Ops, 20:40–21:20.** A session rate limit stopped 13 lanes. All resumed by raw id at 21:20; MSI re-authenticated at 21:20.
83. **sk-strong-7 operator algebras** (fd87db53f7 nodes + artifact; 993aa0cde1 proposal; unreviewed; sk-verify-10 launched to verify).
    - Result: a separable II_1 factor contains G_X in its unitary group for only countably many X. Ozawa, PAMS 132 (2004), Thm 2, applied with Λ = EL_3(F) (EJZ), simple quotients G_X, and distinct kernels via cylinder words.
    - So there are continuum many isomorphism classes of the R^ω-embeddable (T) factors L(G_X), each class countable, inside the Connes-embeddable world where Ozawa asked for embeddable witnesses.
    - Credit: Nicoara–Popa–Sasyk (2007) already give "no separable universal R^ω-embeddable factor"; what the lane adds is the witness family.
    - P1 (+10 text, +4 bibliography, after the Grigorchuk–Medynets remark): ADOPT after a PASS from sk-verify-10, with the verified novelty wording.
    - P2 (+1 line, "no faithful representation into U(R)" via Kirchberg Cor 1.2): ADOPT only if sk-verify-10 confirms that the item used is not the one Thom corrected (item 76).
    - P3 (the trace simplex [trivial, τ_λ]): only together with a PASS for character rigidity.
    - Not in the note, recorded: C*(G_X) is not QWEP; L(G_X) is QWEP; G_X fails AP (recalled, not re-read).
    - Sharpest open target: vN rigidity L(G_X) ≅ L(G_Y) ⇒ flip conjugate or SOE. Famous-hard, and it does not gate the note.
84. **sk-verify-7 parts 3–5** (ef28dd4d20, 6ab268edd3, f2f6824182). Every item PASSes, with no FAIL or GAP.
    - Rev4 gates now open:
      - (c) the unified headline (sk-strong-6/8);
      - (d) the universal host (sk-universal-lef-host-b) + no decidable host (sk-wp-host);
      - the SL_3(Z)/H_3(Z)/BS(1,2) obstruction (sk-sl3z-bandwidth);
      - the separable-factor result (sk-strong-7 P1).
    - Cairn-only PASSes, with their named imports as conditions: sk-lef-growth-all (W8: forward-orbit density sentence), sk-trace-template, sk-k2-recurrent, sk-cartan-counterexample, sk-labbe-2d (W9), sk-measured-subshift, sk-matricial-stability.
    - Second independent reviews continue on the rev4 items: sk-verify-9 (headline + Theorem 2), sk-verify-11 (host, wp-host), sk-verify-12 (sl3z), sk-verify-10 (strong-7 novelty wording and P2).
85. **Character rigidity PASS** (sk-characters-rigidity-a, 591d1248dc): every lemma re-derived. Lemma 1′ fails over q > 2, consistent with the firewall.
    - DECIDED: rev4 carries Theorem "every character of G_X is c·1+(1−c)δ_e". The proof is compressed to ≤ 1 page. Corollaries: L(G_X) is the only II_1 factor representation, trivial IRS, the trace simplex (strong-7 P3).
    - Reader merit: the strongest operator-algebraic statement about G_X, in the line of Bekka's character rigidity for SL_n(Z) and Peterson's conjecture.
    - Budget: 8 pp including this.
86. **sk-cstar-simple** (5b5d267149, 8c01032729, 0da354bcb9; unreviewed, rerouted to sk-verify-13).
    - Root subgroups, GL_n(LC(X,F_2)), the images of [[T]]′ and [[T]], and the cut stabilizers S_y are not confined. Necessary for C*-simplicity, not sufficient.
    - C*-simplicity stays OPEN. Next step: an idempotent Le Boudec–Matte Bon commutator lemma. No note change.
87. **Wave 10 launched (~21:50, ROSTER-H.md).** The user asked "do u want more agents? u have barely any" and "what about free mathematics agents given lots of freedom of what to do". 23 forks:
    - verifiers: sk-verify-11/12/13;
    - literature and referee lanes: sk-answered-questions, sk-prior-art-2, sk-referee-significance;
    - research: sk-iso-rigidity, sk-fp-sofic-host, sk-sofic-host-hamming, sk-decidable-host, sk-lef-proof-compress, sk-two-generators, sk-cstar-simple-2;
    - text: sk-general-statement, sk-questions-section;
    - 8 free lanes, sk-free-1..8.
    - The rev4 referees a/b/c launch when rev4 is ready.

## Rejected (recorded)
- The explicit Kazhdan constant 1/727 in the note (it stays in Cairn).
- The exact centre formula over F_q (it stays in Cairn).
- The L(G_X) property (T) factor sentence: "hyperlinear" already answers Brown's form.
