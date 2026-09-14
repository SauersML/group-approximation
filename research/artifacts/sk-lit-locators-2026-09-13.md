# sk-lit-locators: journal-version check of every locator in the note (2026-09-13)

Lane sk-lit-locators.
- **Subject:** main's `simple_kazhdan_sofic_group.tex` at e80dcf20ad, revision 2, md5 4ad49212…, 386 lines. Line numbers "l.N" refer to that blob. I also checked the extra bibitems of the rev3 draft (`sk/drafts/rev3.tex`, not landed): Ore, Wilson, Kionke–Schesler.
- **Division of labor:** sk-verify-6 (`sk-review-6-2026-09-13-part1.md`) already passed the arXiv versions of Kirchberg, Ozawa, Pestov and Brown. This lane targets the JOURNAL versions.
- **Method:**
  - Publisher PDFs were downloaded on MSI and read locally as page images.
  - Metadata comes from Crossref (`api.crossref.org/works/<doi>`) and zbMATH (`api.zbmath.org`).
  - Where the publisher blocked downloads (World Scientific, ScienceDirect, De Gruyter, AMS), printed secondary sources were used and are named as such.

## 1. Verdict table

| # | Note | Locator / metadata | Journal source read | Verdict |
|---|---|---|---|---|
| 1 | l.111 | EJZ Theorem 1.1 | Invent. Math. 179 (2010), PDF p. 304 | VERIFIED |
| 2 | bib | EJZ 179 (2010) 303–347, doi | PDF header p. 303; Crossref | VERIFIED |
| 3 | l.175 | Kirchberg Theorem 1.1 | Math. Ann. 299 (1994), PDF p. 552 | VERIFIED (flag F6) |
| 4 | bib | Kirchberg 299 (1994) 551–563, doi | PDF header p. 551; Crossref (issue 1) | VERIFIED |
| 5 | l.70 | Stepanov Theorem 4.4 | J. Math. Sci. 95 (1999), PDF pp. 2151–2152 | VERIFIED |
| 6 | bib | Zap. POMI 236 (1997) 166–182; J. Math. Sci. 95 (1999) 2146–2155 | PDF p. 2146 translation line; Crossref | VERIFIED |
| 7 | l.68, l.164 | Kassabov (no locator) | Invent. Math. 170 (2007), PDF p. 297 abstract | VERIFIED |
| 8 | bib | Kassabov 170 (2007) 297–326, doi | PDF header; Crossref | VERIFIED |
| 9 | l.165–166 | Pestov Example 4.5 and Theorem 3.3 | BSL 14 (2008), PDF pp. 456, 461–462 | VERIFIED (journal numbering = arXiv v8) |
| 10 | l.45 | Pestov Open question 9.1 | BSL p. 472 | VERIFIED |
| 11 | bib | Pestov 14 (2008) 449–480, doi | PDF p. 449 header; Crossref (no. 4) | VERIFIED |
| 12 | l.67 | GM Theorem 2.6 | Mat. Sb. 205:6 (2014), Russian original, PDF p. 92 | VERIFIED (numbering of original) |
| 13 | bib | GM Sb. Math. 205 (2014) 843–861, doi | Crossref (issue 6) | VERIFIED |
| 14 | l.77 | Matui Lemma 3.4 and Theorem 4.9 | journal PDF blocked; arXiv v3 source plus GM's printed citations | VERIFIED indirectly |
| 15 | bib | Matui IJM 17 (2006) 231–251, doi | Crossref (no. 2); GM Mat. Sb. bibliography [13] | VERIFIED |
| 16 | l.79 | Thom (no locator) | GGD 4 (2010), PDF pp. 195, 197–198 | VERIFIED |
| 17 | bib | Thom GGD 4 (2010) 195–208, doi | PDF header p. 195; Crossref | VERIFIED |
| 18 | l.44, l.177 | Ozawa p. 527 | IJM PDF blocked; printed citation in Thom GGD p. 198 | VERIFIED indirectly |
| 19 | l.168 | Ozawa Proposition 7.1 | IJM PDF blocked; printed citation in Pestov BSL p. 471 | VERIFIED indirectly |
| 20 | bib | Ozawa IJM 15 (2004) 501–530, doi; arXiv 2003 | Crossref (no. 5); BSL [64]; GGD [Oza04b] | VERIFIED |
| 21 | l.249 | GMpres Theorem 1.1(3) | journal full text blocked (ScienceDirect; API no entitlement) | UNVERIFIED in journal (arXiv v2 only, via sk-review-2 part1) |
| 22 | bib | GMpres J. Algebra 500 (2018) 46–68, doi | Crossref | VERIFIED |
| 23 | l.117, l.281 | Vershik–Gordon (no locator) | Algebra i Analiz 9:1 (1997), PDF pp. 71–80, 95–97 | VERIFIED (credit note F4) |
| 24 | bib | VG Algebra i Analiz 9 (1997) no. 1, 71–97; St. Petersburg Math. J. 9 (1998) no. 1, 49–67 | PDF pp. 71, 97; zbMATH 0898.20016; mathnet; GGD [VG97] | VERIFIED |
| 25 | l.286 | Alekseev–Thom Open problem 6.1 | arXiv:2608.05362 e-print source (no journal version) | VERIFIED |
| 26 | bib | Alekseev–Thom title, 2026 | arXiv abs page (submitted 5 Aug 2026) | VERIFIED |
| 27 | l.264 | Morse–Hedlund (no locator) | — | — |
| 28 | bib | Amer. J. Math. 62 (1940) 1–42, doi | zbMATH 0022.34003 (1–42); Crossref (first page 1) | VERIFIED |
| 29 | l.291 | GPS (no locator) | — | — |
| 30 | bib | GPS Crelle 469 (1995) 51–112 | Crossref 51–112; zbMATH 0834.46053 51–111; GM Mat. Sb. [34] 51–111 | FIX (F2) |
| 31 | l.43 | Brown §11 Question 7 | arXiv preprint only; no journal record found (Crossref title query) | VERIFIED as preprint (sk-review-6) |
| r3 | rev3 | Wilson Theorem A; Math. Z. 174 (1980) 149–157, doi | PDF p. 149; Crossref (no. 2); zbMATH 0424.20028 | VERIFIED |
| r3 | rev3 | Ore Theorem 1; Proc. AMS 2 (1951) 307–314, doi | Crossref (no. 2); zbMATH 0043.02402; AMS PDF blocked | metadata VERIFIED; Theorem 1 not re-read |
| r3 | rev3 | Kionke–Schesler Theorem 1.2; bibitem arXiv 2023 | Crossref doi 10.4171/jca/103 (2024-11-15); EMS page "online first" | FIX (F1); Theorem 1.2 journal numbering unverified |

No locator in the note is wrong. Two bibliographic fixes (F1, F2), one flag (F6), and two optional credit additions (F4, F8).

## 2. Verbatim evidence (journal pages)

- **EJZ, Invent. Math. 179, p. 304:** "Theorem 1.1 Let R be a finitely generated (associative) ring with 1 and n ≥ 3. Let G = EL_n(R), that is, the subgroup of GL_n(R) generated by elementary matrices. Then G has Kazhdan's property (T)." Header p. 303: "Invent math (2010) 179: 303–347 DOI 10.1007/s00222-009-0218-2".
- **Kirchberg, Math. Ann. 299, p. 552:** "Theorem 1.1 A discrete group with property (F) and property T is residually finite." Header p. 551: "Math. Ann. 299, 551-563 (1994)".
- **Stepanov, J. Math. Sci. 95 (1999), no. 2:**
  - p. 2146 footnote: "Translated from Zapiski Nauchnykh Seminarov POMI, Vol. 236, 1997, pp. 166–182."
  - pp. 2151–2152: "4.4. Theorem. Assume that for any proper two-sided ideal I in R, the following conditions hold: (a) [GL(n,R,I), E(n,R)] = E(n,R,I); (b) for any a ∈ GL(n,R), there exist b ∈ E(n,R/I) and α ∈ (R/I)^n (α ≠ 0) such that α_i = (u^b α)_j = 0 for some i, j ∈ {1,…,n}, where u = ρ_I(a) is the image of a in GL(n,R/I). Then the normal structure of GL(n,R) is standard."
- **Kassabov, Invent. Math. 170, p. 297 (abstract):** "As an application we show that the Cayley graphs of the finite groups SL_{3k}(F_p) can be made expanders with a suitable choice of generators." Header: "Invent. math. 170, 297–326 (2007)".
- **Pestov, BSL 14 (2008), no. 4:**
  - p. 456: "Theorem 3.3 (Elek and Szabó [26]). Every sofic group is hyperlinear."
  - p. 461: "So is every LEF group G in the sense of Vershik and Gordon [75], defined by the property that one can embed every finite F ⊆ G into a suitable finite group so as to preserve the partial multiplication."
  - p. 462: "Example 4.5. Every initially subamenable group is sofic."
  - p. 472: "Open question 9.1 (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's property (T). Can it be hyperlinear (sofic)?"
- **GM, Mat. Sb. 205:6 (2014), p. 92** (Sb. Math. 205:6 is the cover-to-cover translation):
  - "Теорема 2.6. Топологическая полная группа любой канторовой минимальной системы является ЛВК-группой."
  - Before it: "Определение 2.5 … Понятие ЛВК-групп было введено Степиным в 1980-х гг. …" (see F8).
  - The original runs pp. 87–108 (22 pages).
- **Thom, GGD 4 (2010):**
  - p. 195 abstract: "This group provides also an example of a sofic Kazhdan group which is not residually finite".
  - p. 197: "a finitely generated hyperlinear (in fact locally embeddable into finite groups (LEF), hence sofic) Kazhdan group which is not residually finite".
  - p. 198: "As Ozawa points out (see [Oza04b], p. 527), the maximal group C*-algebra of G cannot have the local lifting property."
  - p. 208: "[Oza04b] N. Ozawa, About the QWEP conjecture. Internat. J. Math. 15 (2004), 501–530."
- **Pestov BSL, p. 471:** "Theorem 8.5. (Kirchberg [53]; Radulescu [68] Prop. 2.5; Ozawa [64], Prop. 7.1). Let G be a countable group. Then VN(G) embeds into R^ω if and only if G is hyperlinear." p. 479: "[64] ———, About the QWEP conjecture, International Journal of Mathematics, vol. 15 (2004), pp. 501–530."
- **Vershik–Gordon, Algebra i Analiz 9 (1997), no. 1:**
  - p. 71: "… а класс конечно представимых ЛВК групп совпадает с классом конечно представимых финитно аппроксимируемых (ФА) групп [9, 10]."
  - p. 72: "В §2 … показано, что все локально финитно аппроксимируемые группы являются ЛВК и все конечно представимые ЛВК группы являются ФА."
  - p. 72, §1 1°: the definition of LEF (finite K ⊇ H with a group operation ⊙ extending the partial products on H). It matches l.117–119.
  - p. 97: "[9] Стёпин А. М., Замечание об аппроксимируемости групп, Вестн. Моск. ун-та. Сер. 1. Математика, Механика (1984), № 4, 85–87. [10] Stepin A. M., Approximations of groups and group actions. Cayley topology, Ergodic Theory of Z^d-Actions, LMS Lecture Note Series, vol. 228, CUP, 1996, pp. 475–484."
- **Matui** (journal PDF blocked from MSI; World Scientific returns HTML for pdf, pdfplus, pdfdirect and epdf):
  - arXiv:math/0404117 v3 (23 Jul 2005; journal issue Feb 2006) uses `\newtheorem{thm}{Theorem}[section]` with one shared counter.
  - Environments in §3: df 3.1, prop 3.2, prop 3.3, lem 3.4 `DAFsimple`.
  - Environments in §4: lem 4.1–4.4, df 4.5, prop 4.6, lem 4.7, thm 4.8, thm 4.9 `CMsimple`.
  - Lemma 3.4: "… the commutator subgroup D(G) equals to the union ⋃H_m. Furthermore, D(G) is simple if the Bratteli diagram B is simple".
  - Theorem 4.9: "Let (X,φ) be a Cantor minimal system. The commutator subgroup D([[φ]]_0) is simple."
  - Printed confirmation of the journal numbering: GM, Mat. Sb. 205:6, p. 91 cites "[13; теорема 4.9]" (simplicity of [[T]]′), "[13; теорема 5.4]" and "[13; теорема 5.7]", and p. 107 gives "[13] H. Matui, … Internat. J. Math., 17:2 (2006), 231–251". All three agree with the v3 counters (thm 5.4 `Dfg`, thm 5.7).
- **Alekseev–Thom, arXiv:2608.05362** (`main_final.tex`):
  - `\newtheorem{openproblem}[theorem]{Open problem}`, where `theorem` is numbered within sections.
  - `\section{Open problems}` is the sixth numbered section, and its first environment (l.1731) reads: "Are there examples of finitely presented sofic groups with Kazhdan's property (T) that are not residually finite?"
  - The note's paraphrase at l.286–287 is faithful.
- **Wilson, Math. Z. 174 (1980), p. 149:** "Theorem A. Every countable residually finite group G can be embedded in a 2-generator residually finite group Ĝ. Further, Ĝ may be chosen so that, if G is soluble, residually soluble or residually nilpotent, then so is Ĝ."

## 3. Fixes and flags

**F1 (rev3 bibitem, Kionke–Schesler).** The paper is published. Crossref for doi 10.4171/jca/103 gives "Journal of Combinatorial Algebra", online 2024-11-15, with no volume or pages. The EMS article page shows "J. Comb. Algebra (2024), published online first". Theorem 1.2 is checked in the arXiv numbering only; the journal PDF was not obtained.

**F2 (GPS page range).** Crossref's publisher deposit gives 51–112. zbMATH 0834.46053 and the printed bibliography of GM (Mat. Sb. 205:6, p. 108, [34]) both give 51–111. Recommend 51--111, the reviewing-database value.

**F4 (optional credit, Vershik–Gordon).**
- The note cites VG for "A finitely presented LEF group is residually finite" (l.281). VG state and prove it (announced p. 72 as proved in §2), and they credit it to Stepin [9, 10] on p. 71.
- Within this lane's reading (pp. 71–80, 95–97), the numbered §2 statement was not located. So a "\S2" locator rests on VG's own summary.
- Optional: cite Stepin alongside VG.
- Bibdata (zbMATH 0565.20014): A. M. Stepin, *Remark on approximability of groups*, Vestnik Moskov. Univ. Ser. I Mat. Mekh. 1984, no. 4, 85–87; English transl. Moscow Univ. Math. Bull. 39 (1984), no. 4, 90–93.

**F6 (flag, Kirchberg).**
- Thom, GGD 4 (2010), abstract p. 195: "We also point out a mistake in [Kir94], Corollary 1.2 (v) ⇒ (i), and [Kir93], Corollary 7.3 (iii)". Remark 1.6, p. 198, gives the counterexample (almost connected groups).
- The note cites only Theorem 1.1, which is unaffected.
- Any future clause built on Kirchberg's Corollary 1.2 must not use item (v). The optional "(ii) ⇒ (i)" clause (no faithful representation into the hyperfinite II_1 factor) is outside Thom's correction.

**F8 (optional credit, the LEF notion).** GM (Mat. Sb. p. 92, Definition 2.5) credit the notion of LEF groups to Stepin (1980s). VG (p. 71) credit the f.p. LEF ⇒ RF fact to Stepin. The note credits Vershik–Gordon only (l.117). Adding Stepin is a credit choice for main; no locator is wrong.

**Rev3 bibdata that closes sk-lit-credit-audit flags** (zbMATH records):
- Rădulescu: Theta Ser. Adv. Math. 9, Theta, Bucharest (2008), 173–185 (1199.46137).
- Margulis: Probl. Peredachi Inf. 9 (1973), no. 4, 71–80, "Explicit construction of a concentrator", singular (0312.22011). The English translation data is still unverified.
- Hedlund: Amer. J. Math. 66 (1944), 605–620 (0063.01982).
- Ore: Proc. AMS 2 (1951), 307–314 (0043.02402).
- Murray–von Neumann IV: Crossref gives Ann. of Math. 44 (1943), no. 4, first page 716. The end page is still unverified.

## 4. Manuscript proposal (§6 format)

**P1 (F2; recommended; 0 lines).** l.332, current:
```latex
J. Reine Angew. Math. \textbf{469} (1995), 51--112.
```
Replacement:
```latex
J. Reine Angew. Math. \textbf{469} (1995), 51--111.
```
- Trade-off: no cost to the reader; the page range matches the reviewing databases.
- Status: zbMATH plus a printed secondary source, against the Crossref deposit.

**P2 (F1; rev3 only; 0 lines).** Current rev3 draft l.446–449:
```latex
\bibitem{KionkeSchesler}
S.~Kionke and E.~Schesler,
\emph{From telescopes to frames and simple groups},
\href{https://arxiv.org/abs/2304.09307}{arXiv:2304.09307} (2023).
```
Replacement:
```latex
\bibitem{KionkeSchesler}
S.~Kionke and E.~Schesler,
\emph{From telescopes to frames and simple groups},
J. Comb. Algebra, online first (2024).
\doi{10.4171/JCA/103}.
```
- Trade-off: the reader gets the published version.
- Status: Crossref and the EMS page verified. The `[Theorem~1.2]` locator is arXiv numbering (unverified in journal).

**P3 (F4/F8; optional; +4 bibliography lines).** l.281, current:
```latex
A finitely presented LEF group is residually finite~\cite{VershikGordon},
```
Replacement:
```latex
A finitely presented LEF group is residually finite~\cite{Stepin,VershikGordon},
```
New bibitem:
```latex
\bibitem{Stepin}
A.~M. Stepin, \emph{A remark on the approximability of groups},
Vestnik Moskov. Univ. Ser. I Mat. Mekh. (1984), no.~4, 85--87;
English transl., Moscow Univ. Math. Bull. \textbf{39} (1984), no.~4, 90--93.
```
- Trade-off: credit goes to the source VG themselves cite for this fact, at +4 bibliography lines. No new fact to trust.
- Status: bibdata from zbMATH and VG p. 97 (Russian title verified; the English title follows zbMATH's "Remark on approximability of groups"). The paper itself was not read.

**No change** to any other locator: EJZ 1.1, Kirchberg 1.1, Stepanov 4.4, Pestov 3.3/4.5/9.1, GM 2.6, Matui 3.4/4.9, Ozawa p. 527 and 7.1, Alekseev–Thom 6.1, or the metadata of all remaining bibitems.

## 5. Not obtained (bounded)
- World Scientific PDFs of Ozawa and Matui (HTML from MSI for pdf, pdfplus, pdfdirect and epdf).
- ScienceDirect GMpres (HTML; API returns no full text).
- De Gruyter GPS (empty body).
- AMS Ore (Cloudflare challenge).
- EMS JCA Kionke–Schesler (no PDF link on the article page).
- JSTOR Morse–Hedlund (challenge page).
- The numbered §2 statement in VG (pp. 81–94 not read).
