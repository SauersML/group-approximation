# sk-lit-background proposal: background and credit for the note (2026-09-13)

- **Subject:** main's `simple_kazhdan_sofic_group.tex` at revision 2 (e80dcf20ad, md5 4ad49212…, 386 lines). Line numbers "r2 l.N" refer to it. Revision 3 is in assembly, so each "Before" block is quoted verbatim and can be found by text.
- **Evidence:**
  - `research/artifacts/sk-lit-background-2026-09-13-part1.md` (98d07f2f07): Crossref data;
  - `research/artifacts/sk-lit-background-2026-09-13-part2.md` (1db46142dd): verbatim quotes V1–V10 from the arXiv TeX sources.
- **Not duplicated here:**
  - sk-lit-credit-audit (98e268fe22) proposes Kazhdan, Rădulescu/Gromov99/Weiss, Elek–Szabó, Grigorchuk/Champetier, Margulis, McDuff/Murray–von Neumann, Hedlund/Lothaire (its P1–P7).
  - sk-lit-novelty-2 (da70113d45) proposes the credit sentences for rev3's §2: Kionke–Schesler, Schupp/Gorjuškin, Wilson.
  - This proposal covers only what neither has: BG1–BG3. §4 is the consolidated list of every missing citation, with its owner.
- **Status:** literature and credit only. No mathematics changes, no Cairn nodes.

## BG1 (RECOMMENDED): the history of simple Kazhdan groups, r2 l.75–79

The note never says where infinite simple Kazhdan groups come from, or that none was known to be hyperlinear. A top-journal reader needs both to measure the answer (sk-panel-referee-3, B5).

(a) Before (r2 l.75–79):
```latex
an elementary matrix. For derived topological full groups, Matui showed in the same
way that a nontrivial normal subgroup meets a simple union of alternating
groups on towers~\cite[Lemma~3.4 and Theorem~4.9]{Matui}. Thom
constructed a finitely generated Kazhdan LEF group that is not residually
finite~\cite{Thom}, but his example is not simple.
```
After:
```latex
an elementary matrix. For derived topological full groups, Matui showed in the same
way that a nontrivial normal subgroup meets a simple union of alternating
groups on towers~\cite[Lemma~3.4 and Theorem~4.9]{Matui}. Infinite simple
Kazhdan groups arise as quotients of hyperbolic Kazhdan
groups~\cite{GromovHyperbolic} and as Kac--Moody lattices, which gave the
first finitely presented examples~\cite{CapraceRemy}, but none was known to be
hyperlinear~\cite{Ozawa,Pestov}. Thom constructed a finitely generated Kazhdan
LEF group that is not residually finite and so lacks the factorization
property~\cite{Thom}, but his example is not simple.
```
Bibitems. Data are Crossref-verified (part 1, B1); the key `GromovHyperbolic` avoids a clash with sk-lit-credit-audit's `Gromov` (JEMS 1999):
```latex
\bibitem{CapraceRemy}
P.-E. Caprace and B.~R\'emy, \emph{Simplicity and superrigidity of twin building lattices},
Invent. Math. \textbf{176} (2009), 169--221. \doi{10.1007/s00222-008-0162-6}.

\bibitem{GromovHyperbolic}
M.~Gromov, \emph{Hyperbolic groups}, in: Essays in group theory, Math. Sci. Res. Inst. Publ.
\textbf{8}, Springer, New York, 1987, 75--263. \doi{10.1007/978-1-4613-9586-7_3}.
```
(b) Proof text: none. Every clause is a citation.

(c) Length: +4 text lines, +8 bibliography lines.

(d) Reader trade-off: the reader learns the two known sources of infinite simple Kazhdan groups, and that none was known to be hyperlinear, which is the measure of the result. The reader trusts three printed sources and no new mathematics.

(e) Source status:
- **Gromov's quotients:** Thom 0810.2180, main.tex l.96, verbatim in part 2 V1. The primary Gromov 1987 statement was not read. The text says only "quotients of hyperbolic Kazhdan groups", with no "every" and no Tarski-monster claim, so it needs nothing beyond Thom's summary. If a locator is wanted, it is sk-lit-locators' check. Ol'shanskii 1993 (part 1, B1) is the usual careful reference, but I did not read it, so it is not proposed.
- **Caprace–Rémy:** "first infinite finitely presented" is their own words (SimplSuperrigid.tex l.153–154, part 2 V2). Do NOT print "first finitely generated", which their l.1827 says; Thom's Gromov attribution contradicts it.
- **"None was known to be hyperlinear":** Ozawa, arXiv p. 26 / journal p. 527, "It is unknown whether there exists a simple property (T) group Γ which is hyperlinear" (sk-citations part 2); Pestov, Open question 9.1 (V4 context).
- **"and so lacks the factorization property":** Thom's own framing, main.tex l.56: "N. Ozawa observed that there are no hyperlinear groups known which do not have E. Kirchberg's factorization property ... In this note, we give examples of groups with this behaviour." Part 2 V8. This credits Thom for the non-simple precursor of r2 l.173–177. The "so" uses Kirchberg's theorem, which r2 cites at l.174–175.

## BG2 (RECOMMENDED): full credit for "hyperlinear ⟺ L(G) embeds in R^ω", r2 l.168

(a) Before (r2 l.168):
```latex
So $L(G)$ embeds in $\mathcal R^\omega$~\cite[Proposition~7.1]{Ozawa}.
```
After:
```latex
So $L(G)$ embeds in $\mathcal R^\omega$~\cite{Kirchberg,Radulescu},
\cite[Proposition~7.1]{Ozawa}.
```

(b) Proof text: none.

(c) Length: +1 text line. No new bibitem beyond `Radulescu`, which sk-lit-credit-audit P2 adds. If P2 is not adopted, add:
```latex
\bibitem{Radulescu}
F.~R\u{a}dulescu, \emph{The von Neumann algebra of the non-residually finite Baumslag group
$\langle a,b\mid ab^3a^{-1}=b^2\rangle$ embeds into $R^\omega$},
\href{https://arxiv.org/abs/math/0004172}{arXiv:math/0004172} (2000).
```
- Title and date are from the arXiv abstract metadata (part 2).
- The published volume is sk-lit-locators' FLAG.

(d) Reader trade-off: the equivalence is credited as the standard survey credits it. There is no new fact to trust and the cost is one line.

(e) Source: Pestov's guide, hypsof.tex l.799–802, verbatim in part 2 V5: "\begin{theorem}[Kirchberg \cite{kirchberg94}; Radulescu \cite{radulescu00}, Prop. 2.5; Ozawa \cite{ozawa}, Prop. 7.1] Let $G$ be a countable group. Then $VN(G)$ embeds into $R^\omega$ if and only if $G$ is hyperlinear."
- `kirchberg94` is the Math. Ann. 299 (1994) paper already in the note's bibliography (hypsof.tex l.1173).
- CAUTION, not fixed here: in Rădulescu's arXiv v3, 2.5 is a *Definition* (convexsets.tex l.290). So cite him without a locator, as above, and never write "Proposition 2.5". Kirchberg's exact locator is unverified, so he is also cited without one.

## BG3 (OPTIONAL, NOT RECOMMENDED): Connes 1976 at r2 l.40–43

The opening uses $\mathcal R^\omega$ (Brown's question) without naming Connes' embedding problem.
- The one-clause option is "the setting of Connes' embedding problem~\cite{Connes}", with bibitem Connes, Ann. of Math. (2) 104 (1976) 73–115, doi:10.2307/1971057 (part 1, B2).
- Verdict: do not add. The question the note answers is Brown's, Ozawa's and Pestov's, and naming Connes' problem invites a discussion the note does not need.
- If anyone adds it, use **1976**. Pestov's guide says "Connes' 1979 paper" (hypsof.tex l.385), and that is a slip: his own bibitem l.1044–1046 is the 1976 Annals paper.

## §4. Consolidated list: every citation the note still lacks, by owner

| r2 place | what it asserts | citation to add | proposal owner |
|---|---|---|---|
| l.64–65 | property (T) | Kazhdan 1967 | sk-lit-credit-audit P1 |
| l.44–46 | "hyperlinear", "sofic" | Rădulescu; Gromov 1999; Weiss 2000 | sk-lit-credit-audit P2 |
| l.164–166 | sofic ⇒ hyperlinear | Elek–Szabó 2005 | sk-lit-credit-audit P3 |
| l.162–163 | space of marked groups | Grigorchuk 1984; Champetier 2000 | sk-lit-credit-audit P4 |
| l.163–164 | (T) ⇒ expanders | Margulis 1973 | sk-lit-credit-audit P5 |
| l.170–172 | ICC ⇒ II_1 factor; McDuff factor | Murray–von Neumann 1943; McDuff 1970 | sk-lit-credit-audit P6 |
| l.261–264 | Sturmian codings | Hedlund 1944; Lothaire ch. 2 | sk-lit-credit-audit P7 |
| l.75–79 | sources of simple Kazhdan groups; none known hyperlinear; Thom's no-factorization precursor | Gromov 1987; Caprace–Rémy 2009; (Ozawa, Pestov, Thom already cited) | **this lane, BG1** |
| l.168 | hyperlinear ⟺ L(G) ⊂ R^ω | Kirchberg 1994 (in bib); Rădulescu 2000 | **this lane, BG2** |
| rev3 §2 | RF and LEF groups into simple groups | Kionke–Schesler; Schupp; Gorjuškin; Wilson 1980; Ore 1951 | sk-lit-novelty-2 N1; sk-lit-credit-audit §4 |
| l.40–43 | R^ω setting | Connes 1976 | this lane, BG3: not recommended |

## §5. Flags for sk-lit-locators, and data it can close from this lane's evidence
- **Margulis 1973, English translation:** Problems of Information Transmission **9** (1973), no. 4, 325–332, published 1975. Lubotzky arXiv:1105.2389 bibliography l.2279–2281 has "Problemy Peredac(i Informacii 9 (1973), no. 4, 7180. English translation: Problems of Information Transmission 9 (1973), no. 4, 325--332 (1975)". The garbled "7180" is 71–80. This is secondary; no Crossref record.
- **Vershik–Gordon:** Pestov's bibliography (hypsof.tex l.1240) gives "St. Petersburg Math. J. **9** (1998), 49--67". That agrees with the note, and is a second independent confirmation. No Crossref record, no DOI.
- **Weiss 2000:** Pestov's bibliography (l.1250–1253) gives "Sankhy\=a Ser. A 62 (2000), no. 3, 350--359". No Crossref record.
- **Kionke–Schesler:** J. Comb. Algebra, online 15 Nov 2024, doi:10.4171/JCA/103 (Crossref: no volume or pages). The arXiv version 2304.09307's intro theorem (tree-permutations.tex l.188–196) is quoted in part 2 V9. The theorem numbering differs between versions.
- **Ershov, Duke 145 (2008):** pages 309–339 are secondary (Crossref gives no pages). It is only needed if a background sentence on golden groups is added; none is proposed.
