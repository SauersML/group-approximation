# sk-rev4-referee-b: credit, exposition and claims-proved referee of revision 4 (2026-09-13)

Lane sk-rev4-referee-b, per roster `wip/simple-kazhdan-note/swarm/ROSTER-I.md`.
- **Target:** `simple_kazhdan_sofic_group.tex` as landed on main at c8b6021ca9, md5 9144d8536cdca9073d50ffb64b826c00, 771 lines. The md5 was checked on the tip. Line numbers refer to that file.
- **Scope:** credit, citations and locators; whether every claim of the title, abstract and theorem statements is proved or cited in the text; prose doctrine.
- **Out of scope:** correctness in depth (referee a); cuts (referee c).
- **Independence:** I did not read the other rev4 referee reports.

## 0. Verdict
- **ERROR:** none.
- **GAP:** none. Every claim of the title, abstract, Theorems 1–2 and Corollaries 3–5 is proved in the text or cited with a correct locator.
- **UNCLEAR:** four small credit or exposition points (C1–C4), each with a fix of at most one line.
- **Locators the other lanes saw only in arXiv numbering are now checked at source** (§2):
  - Clark–Edie-Michell Cor 4.6: journal PDF;
  - Coulon–Fournier-Facio Thm 1.5: v1 and v3 compiled;
  - Brown §11 Question 7: v3 source;
  - Kionke–Schesler Thm 1.2: arXiv v1 compiled; the journal PDF could not be fetched.
- **Mechanical checks:**
  - 46 cite keys = 46 bibitems (the cite scan joins lines, so multi-line optional arguments are counted);
  - all `\ref` labels resolve;
  - no Codex, OpenAI, Astra, Lean or agent mention;
  - no "hence", "therefore" or "rather than";
  - "first" occurs only mathematically ("first coordinate", "first statement", "online first");
  - no "answers Ozawa's question", no "only known example", no Connes;
  - no British spellings found.
- **Recommendation:** no blocker. Apply C1–C4 in rev4.1 (0–2 net lines).

## 1. Claims and where they are proved or cited

| claim | location | verdict |
|---|---|---|
| G_X infinite, f.g., simple, (T) | Thm 1 via Thm 2, §1–§2 | proved; (T) cited EJZ Thm 1.1 |
| marked limit of SL_{3N}(F_2), expanders for images of a fixed generating set | §1 "Finite simple models", §2 last lines | proved; Margulis, Kassabov cited; C3 on N_k → ∞ |
| LEF, sofic, hyperlinear | §1 end; Brown's formulation | proved; Pestov Ex 4.5, Elek–Szabó Thm 2 |
| EL_n, n ≥ 3 | l.134 "replace 3 by n" | proved (d = n|B_w|) |
| answers Brown (§11 Q7), Ozawa (p. 527), Pestov 9.1 | l.45–53, l.240–256 | proved; Brown Q7 verbatim checked (§2.3) |
| no factorization property, not in U(R), no LLP | l.249–256 | cited Kirchberg Thm 1.1, Cor 1.2 (ii)⇒(i); Ozawa p. 527 |
| Theorem 2 (general engine) | §1 | proved; "matricial" defined in the statement |
| Cor 3: LEF iff subgroup of a simple Kazhdan limit of SL_N(F_2) expanders | §3 proof | proved |
| Cor 4: host iff LEF + countably many types; recursively presented examples | §3 proof, l.403–409 | proved |
| [[T]]′ ≤ G_X | l.412–417; intro l.92–93 | proved as a direct check; C2 pointer |
| no decidable host | l.423–430 | argued; KMS Thm 4.21 (journal numbering, sk-verify-11), Rauzy |
| SL_3(Z) in no G_X | l.432–442 | proved; CFKP credited, no claim to answer CFKP 5.1–5.3 |
| word-problem degrees, every Turing degree | §4 Cor | proved; Morse–Hedlund, Hedlund, Lothaire |
| continuum many L(G_X), each separable factor holds countably many | l.483–494 | proof of Ozawa 2004 Thm 2 invoked; NPS context sentence |
| Questions | §5 | Stepin/Vershik–Gordon, Caprace–Rémy, Alekseev–Thom 6.1 and §5, GPS99, Bezuglyi–Medynets, GPS |

## 2. Locators verified at source (MSI, today)

### 2.1 Clark–Edie-Michell, journal numbering: PASS
- Springer PDF (Algebr Represent Theor (2015) 18:907–916, DOI 10.1007/s10468-015-9522-2), text extracted with pdftotext, l.399–400: "Corollary 4.6 Let G be a Hausdorff, ample groupoid and R a commutative ring with identity. Then A_R(G) is simple if and only if G is effective and minimal, and R is a field."
- arXiv 1403.4684 compiles to the same number (label `thm:feild` → 4.6).
- Crossref: vol 18, issue 4, pp. 907–916. The bibitem matches.

### 2.2 Coulon–Fournier-Facio, Theorem 1.5: PASS, stable across versions
- arXiv 2312.11684 has v1–v3 (v3: "all groups constructed are now 2-generated"). There is no journal reference on arXiv, and a Crossref bibliographic query finds no published record, so "preprint (2023)" is right. Title as printed: "Infinite simple characteristic quotients".
- v3 compiled with labels inserted: the intro theorem at source l.212 (`intro:thm:answer:strong`) is **Theorem 1.5**. Verbatim: "Let Γ be a torsion-free, non-elementary hyperbolic group. Then, for every countable group L, there exists a characteristic subgroup N < Γ such that Γ/N is simple, 2-generated, contains L as a subgroup, and contains an element of order n ∈ ℕ if and only if L does."
- v1 compiled the same way: the corresponding intro theorem (source l.187) is also Theorem 1.5. The body version is Theorem 4.1 in both v1 and v3.
- The note's two uses (l.301–303, l.421–423) need a torsion-free hyperbolic Kazhdan Γ, such as a torsion-free cocompact lattice in Sp(n,1). That is standard and not part of CFF 1.5; the sentence as printed is fine.

### 2.3 Brown, math/0111286: PASS
- arXiv title "Tracial invariants, classification and II_1 factor representations of Popa algebras" matches the bibitem. No journal reference on arXiv, and Crossref finds no published version, so the preprint bibitem is right.
- v3 source, sections in order: 1 Introduction … 8 II_1 Factor Representations of Popa Algebras, 9 Connes' Embedding Problem, 10 Szegő's Limit Theorem, **11 Questions**.
- Item 7 verbatim: "Can an infinite, simple, discrete group with Kazdan's property T be embed into the unitary group of an $R^{\omega}$-embeddable McDuff factor? (Compare with [robertson] where it is shown that no such embedding exists into the unitary group of $L(\mathbb F_n)\bar{\otimes} R$ or, more generally, $L(\Gamma)$ for any a-T-amenable discrete group $\Gamma$.)" So `\cite[\S11, Question~7]{Brown}` and the note's paraphrase at l.45–48 are correct.

### 2.4 Kionke–Schesler Theorem 1.2: PASS in arXiv numbering; journal numbering VERIFY-PENDING
- arXiv 2304.09307 has v1 only. v1 compiled: `thm:embedding-intro` → 1.2. Verbatim: "Let H be a finitely generated, residually finite (amenable) group. There is a finitely generated, residually finite (amenable) group G and an infinite, simple, (amenable) LEF group Q such that (1) there is an embedding ι: H → G, (2) there is a projection π: G → Q, (3) the composition π∘ι is injective."
- Q is finitely generated as a quotient of G, so the note's "every finitely generated residually finite group embeds in a finitely generated simple LEF group" (l.304–306) is faithful.
- Journal: Crossref (10.4171/JCA/103) gives J. Comb. Algebra, published online 2024-11-15, no volume or pages, matching "online first (2024)". The EMS Press file URL (serial-article-files/49177) returned the HTML landing page twice, so the journal numbering was not seen. Low risk: the arXiv v1 intro numbering is 1.1–1.5 and a renumbering would only move the locator.
- The Alekseev–Thom title "Centralizers of sofic approximations of Kazhdan groups" is confirmed on arXiv 2608.05362.

## 3. Findings with verbatim fixes

### C1 (UNCLEAR, credit): simple quotients of hyperbolic Kazhdan groups credited to Gromov 1987 (l.73–74)
Current: `Infinite simple Kazhdan groups arise as quotients of` / `hyperbolic Kazhdan groups~\cite{Gromov87} and as Kac--Moody lattices, some`
- The note gives no locator in Gromov 1987 and no lane has seen one.
- Checked at source: Coulon–Fournier-Facio's own introduction (arXiv v3 source l.244) credits the simple-quotient construction for "negatively curved" groups to Ol'shanskii 1979 ("Versions of this construction can be found e.g. in [Ol'79]"), and small cancellation to Ol'shanskii 1991, Gromov 2001 and others. It does not credit Gromov 1987. The sentence is true, but its attribution is unverified.
- Fix (0 net lines, cites a statement checked at source today): `hyperbolic Kazhdan groups~\cite{Gromov87},~\cite[Theorem~1.5]{CoulonFournierFacio} and as Kac--Moody lattices, some`. Alternatively keep Gromov87 with a verified locator.

### C2 (UNCLEAR, exposition, 0 lines): forward pointer for [[T]]′ ≤ G_X (l.92–93)
"It is also a subgroup of $G_X$." is proved only in §3 (l.412–417) with no pointer. Fix: `It is also a subgroup of $G_X$ (Section~\ref{sec:lef}).`

### C3 (UNCLEAR, exposition, 0 lines): reason for N_k → ∞ (l.235–237)
"…$G$ is LEF, and $N_k\to\infty$." gives no reason. Fix: `…$G$ is LEF, and $N_k\to\infty$ as $G$ is infinite.`

### C4 (UNCLEAR, credit, optional, 0 lines): "Matui showed in the same way" (l.100–103)
Matui's Lemma 3.4 works with alternating groups on towers, not with a commutator in GL_d(F_2). "In the same way" can read as a claim that his argument is ours. Referee (b) of rev3 suggested softer wording; it has not been applied. Fix: `Matui showed by a similar argument that a nontrivial normal subgroup meets a simple union of alternating groups on towers~\cite[Lemma~3.4 and Theorem~4.9]{Matui}.`

### Checked and correct, no change
- **Credit sentences:** Rădulescu, Gromov99/Weiss, Thom (non-simple, not RF, so no factorization property), Pestov–Kwiatkowska quote, EJZ, GM Thm 2.6, Kassabov, Matui/Juschenko–Monod, Stepanov Thm 4.4 with Clark–Edie-Michell Cor 4.6, Vershik–Gordon (LEF), Grigorchuk/Champetier, Margulis.
- **Brown's formulation:** Kirchberg Thm 1.1 and Cor 1.2, McDuff, Ozawa Prop 7.1 and p. 527.
- **§3 credit paragraph:**
  - Gorjuškin/Schupp;
  - CFF Thm 1.5;
  - Kionke–Schesler Thm 1.2, with their question stated as raised, not answered ("For LEF groups the next corollary answers the analogous question");
  - Boone–Higman as a parallel;
  - Wilson + Kionke–Schesler and Higman + CFF for each property alone;
  - KMS Thm 4.21 + Rauzy.
- **SL_3(Z) paragraph:** credits CFKP "similarly" and makes no priority claim.
- **P1 paragraph:** "The proof of~[Theorem 2]" (Ozawa 2004) is credited, NPS is context, and there is no priority claim.
- **Questions:** Alekseev–Thom 6.1 and §5 are faithful; "A sofic example would not be LEF" follows from Stepin/Vershik–Gordon.
- **Origin paragraph:** facts only; no OpenAI/Codex/Astra.

## 4. Not checked
- Gromov 1987 itself (C1).
- The Kionke–Schesler journal PDF.
- Journal numbering of Ozawa 2004 Thm 2 (sk-verify-10 used arXiv v2).
- Rauzy's journal numbering for Proposition 26 and Lemma 27 (Crossref metadata only, from sk-answered-questions).
