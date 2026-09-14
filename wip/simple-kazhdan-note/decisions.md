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

## Rejected (recorded)
- The explicit Kazhdan constant 1/727 in the note (it stays in Cairn).
- The exact centre formula over F_q (it stays in Cairn).
- The L(G_X) property (T) factor sentence: "hyperlinear" already answers Brown's form.
