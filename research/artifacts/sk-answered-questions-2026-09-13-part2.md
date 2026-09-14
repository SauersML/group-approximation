# sk-answered-questions: printed questions answered or sharpened by the note's results (part 2: the table)

Lane sk-answered-questions, 2026-09-13 ~22:40 CDT. Continues part 1 (fb104eec26), whose §0 defines R1–R8. Literature facts only: no Cairn claims.

## 0. Method and bound
- Sources: arXiv PDFs downloaded to MSI `/scratch.global/sauer354/sk/sk-answered-questions/` and extracted with poppler 25.11. Kourovka, Kionke–Schesler, Cornulier (Bourbaki), Grigorchuk–Medynets, Katzlinger and Juschenko's text were reused from sk-questions-ggt's directory. The Vershik–Gordon Russian PDF came from sk-verify-6's directory.
- For each source I grepped `Question N|Problem N|Conjecture N|open question|natural question|would be interesting|remains open|we do not know|is unknown|open problem`, then read the surrounding windows. Keyword greps were added per result (universal, word problem, Turing, distort, nilpotent, Heisenberg, character, II_1, expander, embed … simple).
- Page numbers are arXiv page numbers counted from form feeds, unless marked "journal".
- Web searches: seven, for Boone–Higman analogues, universal LEF/sofic groups, Capraro–Lupini problems, Popa's problem lists, Cyr–Franks–Kra–Petite, Turing degrees of simple groups, character rigidity, and Heisenberg subgroups of topological full groups.
- Nothing was read end to end. The bound is "every printed question located by these greps".

## 1. Rows

**ANSWERED as printed (already in the note):**

| # | Printed text (verbatim) | Source, locator | Result |
|---|---|---|---|
| A1 | "Can an infinite, simple, discrete group with Kazdan's property T be embed into the unitary group of an $R^{\omega}$-embeddable McDuff factor?" | Brown 2001, §Questions, Q7 (arXiv:math/0111286; quoted from source in sk-strong-7 §1.3) | R1, in the note |
| A2 | "It is unknown whether there exists a simple property (T) group Γ which is hyperlinear." | Ozawa, *About the QWEP conjecture*, arXiv:math/0306067v2 p. 26; journal p. 527 as cited by Thom (sk-verify-6) | R1, in the note |
| A3 | "Open question 9.1 (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's property (T). Can it be hyperlinear (sofic)?" | Pestov, BSL 14 (2008), arXiv:0804.3968v8 p. 21 | R1, in the note |
| A4 | "… it remains in particular unknown whether finitely generated simple Kazhdan groups can be hyperlinear/sofic." | Pestov–Kwiatkowska, arXiv:0911.4266 p. 28 (sk-questions-ggt A1) | R1, same lineage |
| A5 | the Elek–Szabó question whether every sofic Kazhdan group is residually finite | through Thom's abstract ("answering a question from [ES05]") | R1 also answers it, but Thom answered it first; not needed |

**The analogue of a printed question, answered completely:**
- **B1. Kionke–Schesler**, *From telescopes to frames and simple groups*, arXiv:2304.09307v1 p. 2:
  > "it is natural to ask which groups embed into finitely generated, simple amenable groups. As far as we know, a complete answer to that question seems yet to be out of reach."
  - R2 answers the LEF analogue completely for finitely generated groups: exactly the LEF groups embed in finitely generated simple LEF groups, and the host can be Kazhdan. If item 71(d) passes, the answer extends to countable groups.
  - The amenable question itself is untouched: Kazhdan hosts are never amenable.
  - Status of R2: reviewed (three PASSes; in rev3).

**Framing: printed theorems with the same shape:**
- **F1. Kourovka Notebook 20.7 (J. Belk)**, arXiv:1401.0300, printed p. 147:
  > "(W. Boone and G. Higman) Does every finitely generated group with solvable word problem embed into a finitely presented simple group? It is known that every such group embeds into a simple subgroup of a finitely presented group (W. Boone, G. Higman, J. Austral. Math. Soc., 18, no. 1 (1974), 41–53)."

  Belk–Bleak–Matucci–Zaremsky, *Progress around the Boone–Higman conjecture* (arXiv:2306.16356), Corollary 3.7:
  > "A finitely generated group has solvable word problem if and only if it embeds into a simple subgroup of a finitely presented group."
  - R2 is the LEF counterpart of this characterization. Neither answers the other.
  - Crossref: W. W. Boone and G. Higman, *An algebraic characterization of groups with soluble word problem*, J. Austral. Math. Soc. 18(1) (1974) 41–53, doi:10.1017/S1446788700019108.
- **F2. Thompson (1980), Darbinyan–Steenbock (2025)**, arXiv:2504.12707 pp. 1, 4:
  > "every finitely generated group G with decidable word problem Frattini embeds into a finitely-generated simple group H that also has decidable word problem" [Tho80]

  Theorem 1.9 extends this to recursively enumerable families. Remark 1.10 (Boone–Rogers 1966): recursive enumerability cannot be replaced by countability.
  - This is the prior art without (T) or LEF for sk-decidable-host.
  - [Tho80]: R. J. Thompson, *Embeddings into finitely generated simple groups which preserve the word problem*, in Word problems II (Oxford 1976), Stud. Logic Found. Math. 95, North-Holland, 1980, 401–441 (as printed in the arXiv:2504.12707 bibliography; not Crossref-checked).

**Prior art to credit:**
- **P1. Rauzy**, *Remarks and problems about algorithmic descriptions of groups*, IJAC 35(7) (2025) 1019–1053, doi:10.1142/S0218196725500328 (Crossref). arXiv:2111.01190v2 p. 8, Proposition 26:
  > "The set of finitely presented residually finite groups is not computably enumerable (for νF P ), and furthermore it cannot be contained in a νF P -c.e. set of finitely presented groups with uniformly solvable word problem."

  The proof of Lemma 27 uses a single host:
  > "it is possible to embed the restricted direct product of all the groups in C in a finitely generated group with solvable word problem. The time complexity of the word problem in this group constitutes the desired asymptotic upper bound."
  - That argument, with Kharlampovich–Myasnikov–Sapir (Bull. Math. Sci. 7(2) (2017) 309–352, doi:10.1007/s13373-017-0103-z, Crossref), is the time-complexity core of sk-wp-host Theorem A (`no-decidable-group-contains-every-fp-rf-group`, R4). sk-wp-host already credits KMS. Rauzy is the nearest printed argument and should be cited next to KMS if R4 enters the note.
- **P2. Chifan–Ioana–Osin–Sun**, through Chifan–Drimbe–Ioana arXiv:2205.07442 p. 2:
  > "it was shown in [CIOS21, Corollary 2.7] that T contains a continuum {L(G_i)}_{i∈I} of nonisomorphic property (T) group II1 factors."
  - A continuum of property (T) group factors is known. R7's difference must be R^ω-embeddability, and the witnesses being LEF simple groups. This bears on sk-verify-10's novelty wording.

**VARIANT only:**
- **V1. Ozawa**, *There is no separable universal II_1-factor*, arXiv:math/0210411v2 p. 2 (PAMS 132 (2004)):
  > "In connection with Connes' embedding problem [C], it would be interesting to know whether all (or at least one of) Γα 's are embeddable into the unitary group U(Rω ) of the ultrapower Rω of hyperfinite II1 -factors."
  - The Γ_α are Gromov's limits of hyperbolic groups, so R7 does not answer this. R7 runs the same countability argument inside the R^ω-embeddable world.
  - Wording for the note: "Ozawa remarked …; his argument applies to the G_X, which are hyperlinear". Not "answers Ozawa".
  - R7 is unreviewed (sk-verify-10).
- **V2. Cornulier**, Séminaire Bourbaki 1064, arXiv:2002.09342, "Problèmes et questions ouvertes", (2e), for an infinite minimal subshift ϕ:
  > "Peut-on donner des résultats généraux sur la structure des sous-groupes élémentairement moyennables de [[ϕ]] ?"
  - R5, corollary C1 (PASS by sk-verify-8): finitely generated subgroups of [[T]] ≤ GL_1(LC(X,F_2)⋊Z) have no distorted elements of infinite order.
  - So H_3(Z) and BS(1,n) are not subgroups of [[ϕ]]. With Cyr–Franks–Kra–Petite's remark (arXiv:1611.05913v2 p. 13, "the Heisenberg group is a subgroup of any finitely generated, torsion-free, nonabelian nilpotent group"), every finitely generated nilpotent subgroup of [[ϕ]] is virtually abelian, since it is virtually torsion-free.
  - That last consequence is my two-line derivation and unreviewed. It is a general structural restriction, a partial answer to an informal question.
  - Novelty is not established. Not found in the Cornulier, Grigorchuk–Medynets, Katzlinger or Matte Bon greps, or in one web search.

**NOT ANSWERED: nearby printed questions (recorded against overclaiming):**
- **N1. Alekseev–Thom**, arXiv:2608.05362v1 p. 18:
  > "Open problem 6.1. Are there examples of finitely presented sofic groups with Kazhdan's property (T ) that are not residually finite?"

  G_X is not finitely presented. The note's Q1 cites it.
- **N2. Cyr–Franks–Kra–Petite**, arXiv:1611.05913v2 p. 13, Questions 5.1–5.3:
  > "Question 5.1. Does the discrete Heisenberg group embed into the automorphism group of a one-dimensional shift? More generally, does the automorphism group of a one-dimensional shift have a distorted element of infinite order?"

  > "Question 5.3. Does a group with exponentially distorted elements, for example SL(3, Z) or the Baumslag-Solitar group BS(1, n), embed into the automorphism group of some positive entropy shift?"

  R5 concerns GL_m(LC(X,F_q)⋊Z) and [[T]], not Aut(X). No answer. Theorem D is the matrix analogue of their Corollary 3.10; their paper is the nearest prior, as sk-sl3z-bandwidth already credits. A distortion element in Aut of the full shift exists: arXiv:2208.00685 (search result, not opened).
- **N3. Bishop–Schesler**, arXiv:2509.12161v2 p. 2:
  > "Question 1.1. Does every finitely generated residually finite group G with solvable word problem embed in a finitely generated branch group with solvable word problem?"

  The hosts in this note are not branch groups. Relevant to sk-decidable-host as a neighbour.
- **N4. Darbinyan–Steenbock Question 2** (a quasi-isometric Boone–Higman for left-orderable groups): unrelated.

**Checked, nothing bearing on R1–R8:**
- Pestov BSL Open questions 2.6, 3.4, 3.8, 3.9, 4.9–4.11, 5.3, 6.2, 8.7, 8.8, 9.2–9.6, 11.1;
- Capraro–Lupini Open Problems I.4.2 and II.3.3, and the remark at text l.2214 (universal sofic groups in models of set theory);
- Lubotzky (arXiv:1105.2389) Conjectures 2.5, 2.20, 2.25, 2.29 and Open Problem 2.28;
- Popa, "Some open problems on II_1 factors of group actions" (Fields 2007), all Q's (relative (T), outer automorphism groups, fundamental groups, W*/OE superrigidity, Cartan uniqueness);
- Ioana ICM survey arXiv:1712.00151 (Connes rigidity for PSL_m(Z) open);
- Peterson–Thom arXiv:1303.4007 (only an almost-homomorphism remark, text l.1131);
- Dudko–Medynets arXiv:2602.16885 (whether A(G) = D(G); product measures);
- Alekseev–Thom Open problem 6.2;
- Belk–Bleak–Matucci–Zaremsky arXiv:2309.06224 Questions 1.1–1.6; the progress survey Problem 2.7 (an explicit f.p. group containing GL_n(Q));
- Kharlampovich–Myasnikov–Sapir; Andrews–Ho arXiv:2402.01882;
- Kionke–Schesler arXiv:2106.08742 Question 2.15;
- Xin Ma arXiv:2209.00580 Question 1.1 (Jiang–Li–Zhang);
- Juschenko Appendix C.31–C.38;
- Vershik–Gordon (Russian): open questions on group algebras, on distinguishing amenable groups inside LEF groups, extensions, central extensions, approximable actions;
- Cornulier Bourbaki (1)–(8) other than (2e).

**Kourovka greps with no answered problem:**
- universal group, Turing, distort (8514: left-orderable), II_1 (0 hits), expander (18.108/109);
- "embedded into a simple" (6253: t.d.l.c.);
- word problem: 5.15, 5.16, 20.7 (F1).

## 2. Per-result verdict
- **R1:** answers Brown Q7, Ozawa (survey p. 527), Pestov 9.1 and Pestov–Kwiatkowska p. 28. All are in the note's lineage already. Nothing new to add.
- **R2:** completely answers the LEF analogue of Kionke–Schesler's printed question (B1), and parallels Boone–Higman (F1). This is the best new framing for the introduction.
- **R3** (universal host): no printed question found.
- **R4** (no decidable host): prior art P1 (Rauzy Prop. 26 and Lemma 27, plus KMS). Credit it if R4 enters the note.
- **R5** (no distortion): nearest prior Cyr–Franks–Kra–Petite; their Questions 5.1–5.3 are untouched; partial structural answer V2 for [[ϕ]].
- **R6** (Turing degrees): no printed question found. Camm and Clapham background is handled by referee (b) C4.
- **R7** (separable factors): variant V1 of Ozawa's remark; prior art P2 for the continuum of (T) group factors.
- **R8** (characters): no printed question found (bounded: Peterson–Thom, Dudko–Medynets 2026, one web search).
- **Marked limits / expanders:** no printed question found (Lubotzky's conjectures unrelated).
