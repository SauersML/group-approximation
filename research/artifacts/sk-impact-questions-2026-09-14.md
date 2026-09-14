# sk-impact-questions: printed questions the simple Kazhdan note answers or bears on (2026-09-14)

Lane sk-impact-questions. Base: rev4.5 on main (8b36733d78), md5 29d63f7944bccccbf9a91b0b2714c0b4. Literature facts only: no claim nodes, no .tex edits, no verify-queue lines.

## 0. Bound
**Already on main, read first and not repeated:**
- sk-answered-questions part1, part2 and proposal;
- sk-kourovka-hunt;
- sk-questions-ggt parts 1–2, with its cached texts at MSI `/scratch.global/sauer354/sk/sk-questions-ggt`;
- sk-prior-art-2/3, sk-lit-novelty-2, sk-verify-10;
- `pestov91-priority-credit-2026-09-13` §0 and §2.2.

**New sources read this pass** (e-print TeX or PDF text on MSI `/scratch.global/sauer354/sk2/sk-impact-questions/src`):
- **Read in full:**
  - Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, the author's total PDF (`KazhdanTotal.pdf`): Chapter 7, "A short list of open questions", text l.12679–12830. Greps over the rest of the book.
  - Arzhantseva, *Asymptotic approximations of finitely generated groups*, the author's PDF (`arzh.txt`).
- **Kourovka Notebook, 2026 edition** (`21tkt.tex`, arXiv:1401.0300 e-print). Greps: marked group, limit(s) of finite, LEF, locally embeddable, hyperlinear, sofic, expander, Kazhdan, (T).
- **Expanders and (T) for rings:**
  - Ershov–Jaikin-Zapirain arXiv:0809.4095 (`EL_n0909.tex`);
  - Ershov–Jaikin-Zapirain–Kassabov arXiv:1102.0031 (`2014gradedT0310.tex`);
  - Kassabov math/0502237; Kassabov–Nikolov math/0502112.
- **Cayley topology:** Mimura–Sako and Mimura–Ozawa–Sako–Suzuki, Parts I–III: arXiv:1310.4736, 1804.10614, 1402.5105.
- **Other e-prints:** Goldbring arXiv:2109.12682; Ozawa arXiv:1212.1700; Gohla–Thom arXiv:2403.09582; Nikolov–Schneider–Thom arXiv:1703.06092; arXiv:2508.17392; Peterson arXiv:2605.16669; Fournier-Facio arXiv:2608.02025; arXiv:2604.19174; arXiv:2410.02913.
- **For lineage checks:** Brown math/0111286 and Ozawa math/0306067, both e-print TeX.
- **Re-grepped from cached texts:** Thom ICM 2018 (arXiv:1712.01052), Nekrashevych arXiv:1511.08241, Capraro–Lupini arXiv:1309.2034, Alekseev–Thom arXiv:2608.05362 and 2512.15494, Kun–Thom arXiv:1901.03963, arXiv:2008.12954, Glebsky arXiv:1506.06940, arXiv:2305.00248.

**Method:**
- Greps for question/problem/conjecture environments and for "open problem | natural question | would be interesting | remains open | is unknown | not known | we do not know", combined with simple, Kazhdan, (T), LEF, sofic, hyperlinear.
- About 12 web searches.

**Not obtained:**
- the AIM problem lists: AIMPL pages returned 404 in sk-questions-ggt's fetch, and one web search found none;
- the Brown–Ozawa book: no e-print;
- the de la Harpe 2002 survey: secondary only;
- the World Scientific PDF of Ozawa's IJM paper: MSI got an HTML page.

## 1. The note's printed lineage, re-verified at source: no error
| Note (rev4.5) | Source text, verbatim | Locator | Verdict |
|---|---|---|---|
| l.47–50, Brown §11 Q7 | "Can an infinite, simple, discrete group with Kazdan's property T be embed into the unitary group of an $R^{\omega}$-embeddable McDuff factor?" | math/0111286 e-print `main.tex` l.3159–3161; `\section{Questions}` (l.3112) is the 11th `\section` | MATCHES "§11, Question 7" |
| l.51–53, Ozawa | "It is unknown whether there exists a simple property $\mathrm{(T)}$ group $\G$ which is hyperlinear. By the above theorem, the full $C^*$-algebra $C^*\G$ of such a group $\G$ cannot have the LLP." | math/0306067 e-print `main.tex` l.2190–2192 | MATCHES, including the LLP clause. Journal "p. 527" not verified here (carried from Thom's citation, sk-verify-6) |
| l.53–54, Pestov 9.1 | "Open question 9.1 (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's property (T). Can it be hyperlinear (sofic)?" | arXiv:0804.3968 text l.1254 | MATCHES |
| l.99–102, Pestov–Kwiatkowska | "Consequently, a hope to use property (T ) in order to construct non-hyperlinear groups is a bit diminished now, but surely not gone, as it remains in particular unknown whether finitely generated simple Kazhdan groups can be hyperlinear/sofic." | arXiv:0911.4266 text l.1380–1384 | the paraphrase is faithful |
| l.288–289, Kionke–Schesler | "it is natural to ask which groups embed into finitely generated, simple amenable groups" | arXiv:2304.09307 text l.87 | MATCHES |
| l.517–519, Alekseev–Thom | "Open problem 6.1. Are there examples of finitely presented sofic groups with Kazhdan's property (T) that are not residually finite?" | arXiv:2608.05362 text l.961 | MATCHES |

## 2. New rows

### ANSWERED as printed, not cited by the note
**I1. Arzhantseva 2014.** §3, "New idea: approximate 'easy' groups by 'complicated' ones":
> "In particular, the following is unknown. … — Does there exist an infinite simple sofic group with Kazhdan's property (T)?"

- **Locator.** Author PDF text l.231–232. The published page is p. 11, per `pestov91-priority-credit-2026-09-13` §2.2, which read the Springer version.
- **Bibliographic data,** Crossref-checked this pass: DOI, title, container "Trends in Mathematics / Extended Abstracts Fall 2012", pages 7–15, 2014. The author's publication list says 7–16.
- **Why answered.** Theorem 1 makes $G_X$ infinite, simple and Kazhdan. It is LEF, hence sofic [Pestov, Example 4.5], as the note already says. Model test: the Thue–Morse subshift. Nothing beyond "infinite minimal" is used.
- **Her own example.** Published Theorem 11, p. 13 (author PDF Theorem 3.3, l.318–319): "there exists an infinite simple asymptotically residually finite (hence, asymptotically sofic) group with Kazhdan's property (T)". It is a torsion-free Tarski monster quotient of a hyperbolic Kazhdan group, via Ol'shanskii.
  - Definition 9 (author PDF 3.1) lets the generating set $S_n$ change with $n$, so this example does not answer the question.
  - The same text lists the question as unknown.
- **Status on main.** Recorded in `pestov91-priority-credit-2026-09-13` §0 and §2.2, for the Pestov 9.1 writeup. It is absent from the note and from every sk-* literature artifact: sk-answered-questions, sk-questions-ggt, sk-kourovka-hunt, sk-prior-art-2/3, sk-lit-novelty-2.
- **Earlier answers: none found.**
  - Her citations page lists 12 citing works: Brude–Sasyk 2020; Capraro–Lupini 2015; Cavaleri thesis 2016; de Chiffre thesis 2019; de Chiffre–Glebsky–Lubotzky–Thom 2020; Climenhaga–Knieper–War 2021; Dadarlat 2021; Enders–Shulman 2019; Eilers–Shulman–Sørensen 2020; Glebsky 2017; Mimura–Sako 2021; Pueschel thesis 2016.
  - By title, none concerns simple Kazhdan groups. Only Capraro–Lupini and Glebsky were grepped, and neither answers it.
  - One web search found no printed answer.
  - This agrees with `pestov91-priority-credit` §0: no earlier or independent answer in print.

### BEARS ON results that are not in the note
**I2. Bekka–de la Harpe–Valette (Cambridge 2008), Chapter 7, question (7.9), p. 301.**
> "(7.9) Does there exist an infinite group with Kazhdan Property (T) which is not of uniform exponential growth? See the discussion in [Harpe–02]."

- **Locator.** `KazhdanTotal.txt` l.12766–12768. This is the primary source for de la Harpe's question; sk-kourovka-hunt M3 had it only through Sauer–Schesler arXiv:2606.15945 l.157.
- **Relation to Cairn.** The Thue–Morse $G_X$ has non-uniform exponential growth (`simple-kazhdan-lef-group-of-non-uniform-exponential-growth`, sk-verify-14 PASS), so it is such a group.
- **Verdict: SHARPENED.** The first printed answer is Sauer–Schesler (per M3, not re-read here); ours adds simple and LEF.
- **For the paper.** No change, since rev4.4 dropped growth from the scope. For Cairn: add the (7.9) locator to that node's background.

### NOT BEARING, recorded against overclaiming
- **BdlHV (7.10)** (l.12770): "Does there exist a countable infinite Kazhdan group Γ such that the subset {π ∈ Γ̂ : dim(π) < ∞} is dense in the unitary dual Γ̂ of Γ?"
  - $G_X$ has no nontrivial finite-dimensional unitary representation: the image would be a finitely generated linear group, which is residually finite by Mal'cev, while $G_X$ is simple and not residually finite.
  - BdlHV (7.1)–(7.8) and (7.11)–(7.15): unrelated.
- **Ershov–Jaikin-Zapirain–Kassabov** (arXiv:1102.0031, l.6524–6536), Conjecture (b): "A family $\mathcal F$ of non-abelian finite simple groups has a mother group with property $(T)$ if and only if $\mathcal F$ contains only finitely many finite simple groups of Lie type of rank $1$."
  - $G_X$ is simple, so it is not a mother group. The family $\SL_{3N}(\F_2)$ already has one, EL_3 of a free algebra (Kassabov; EJZ).
- **Ershov–Jaikin-Zapirain** (arXiv:0809.4095, l.2841–2843): "it would be interesting to determine whether the analogues of the groups $EL_n(R)$ and $St_n(R)$ corresponding to other root systems have property $(T)$." Type A only in the note.
- **Thom, ICM 2018** (arXiv:1712.01052, text l.277–278): "it seems to be an open problem if there exist Sol-approximated simple groups."
  - $G_X$ is approximated by simple groups, not solvable ones.
  - Question 2.5 (finitely presented Sol-approximated ⇒ residually finite-solvable) is unrelated.
- **Gohla–Thom** (arXiv:2403.09582, l.467–469): "Is there a residually finite group, which is not stable in finite actions?" Unrelated.
- **Kassabov** (math/0502237, l.408–420): Lubotzky–Weiss Problem 5.1 and Conjecture 5.4, already answered in the literature. Unrelated.
- **Mimura–Ozawa–Sako–Suzuki III** (arXiv:1402.5105, l.100–103): Roe's question on telling expanders apart. Unrelated. The theorem at l.675 ("the set of all $k$-marked property $(\mathrm{T})$ groups is open") is background only.
- **Kourovka 2026** (`21tkt.tex`):
  - l.7253: branch groups with (T);
  - 14.34, l.21354–21360: a profinite group with amenable and Kazhdan dense subgroups;
  - 18.109, l.10979;
  - l.14026: "Is every group sofic?";
  - l.21758–21766: already answered.

  None bears on the note. No Kourovka problem asks for simple Kazhdan groups that are LEF, sofic or marked limits.
- **No simple Kazhdan approximation question** in: Goldbring, Ozawa 1212.1700, Peterson 2605.16669, Fournier-Facio 2608.02025, 2604.19174, 2410.02913, 2508.17392 (Conjecture l.299), Kassabov–Nikolov math/0502112 l.400, Nekrashevych (no Kazhdan hits), Capraro–Lupini.

## 3. Per-result verdict (rev4.5)
- **Theorems 1 and 2:** answer Brown §11 Q7, Ozawa (e-print l.2190), Pestov 9.1 and Pestov–Kwiatkowska, and also Arzhantseva 2014 p. 11, which the note does not yet cite.
- **Corollary 3:** the LEF analogue of Kionke–Schesler's question, with the Boone–Higman–Thompson shape (sk-answered-questions B1, F1–F2). Nothing new.
- **Corollary 4:** no printed question found (sk-answered-questions R3).
- **Corollary 5:** no printed question found beyond Kourovka 4.60 (sk-kourovka-hunt).
- **Questions section:** Alekseev–Thom 6.1 is cited correctly.

## 4. Proposal (reader merits; main decides)

### P1 (RECOMMEND): one credit sentence after l.102
It goes right after the Pestov–Kwiatkowska sentence, which ends "…can be hyperlinear~\cite{PestovKwiatkowska}."
```latex
Arzhantseva listed the existence of an infinite simple sofic group with
property~\textup{(T)} among open questions, and gave an infinite simple
Kazhdan group that is asymptotically residually finite, a weaker property
in which the generating set may change with the radius~\cite{Arzhantseva}.
```
Bibitem, alphabetical after `AlekseevThom`:
```latex
\bibitem{Arzhantseva}
G.~Arzhantseva, \emph{Asymptotic approximations of finitely generated
groups}, in: Extended Abstracts Fall 2012, Trends Math. Res. Perspect. CRM
Barc. \textbf{1}, Springer, Cham (2014), 7--15.
\doi{10.1007/978-3-319-05488-9_2}.
```
- **Length:** +4 text lines, +5 bibliography lines. A short form (+2 lines) stops after "open questions" and loses the credit clause.
- **Trade-off:** the reader sees a fourth printed form of the question, from a 2014 list of open problems on metric approximations, and the nearest earlier simple Kazhdan example, whose approximation property is weaker. Ozawa stays first (`pestov91-priority-credit` §0).
- **Wording checks:**
  - "listed … among open questions" matches "In particular, the following is unknown." with the question as a list item.
  - "gave", not "constructed": the example is Ol'shanskii's torsion-free Tarski monster with (T).
  - No page locator: the published page (p. 11) was read by the Pestov 9.1 lane, not by this lane. Use `\cite[p.~11]{Arzhantseva}` if main accepts that record.
  - The series abbreviation is not checked against MathSciNet.
- Keep "The groups below answer all three forms positively" (l.54–55): Arzhantseva's question is the sofic form of Pestov's.

### P2 (optional, no text change): the Ozawa page
The e-print sentence is verified (l.2190). This lane could not open the journal PDF, so "p. 527" still rests on Thom's citation.

### Questions section: no sentence proposed
Every nearby printed question is either answered, already cited, or unrelated (§2).
