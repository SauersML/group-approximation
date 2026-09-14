# sk-pdf-visual: typesetting and visual audit of revision 4.3 (2026-09-14)

Lane sk-pdf-visual, a typesetting referee for `simple_kazhdan_sofic_group.tex` rev4.3 (main 696c4b602e, md5 0648e5f876e467e21ebf475e08b8ee92; the local copy matches). No .tex edits. Every fix below is verbatim LaTeX, and none adds a line except where marked.

## 0. Verdict
- **Compile** (MSI /scratch.global/sauer354/sk/pdf-visual, texlive/2025, pdflatex ×3, tex md5 identical on both ends): 0 errors, 0 overfull, 0 undefined, 1 underfull hbox (the Champetier bibitem, badness 1072, source l.610–612), 9 pages, US letter 612×792.
- **The GHA draft PDF on main** (commit cc5dc9168, github-actions[bot], "build: update simple Kazhdan PDF (draft; unattested)") matches this build: 9 pages, the same 21 embedded font subsets, and identical extracted text (33238 characters). The CI build is correct.
- **No typesetting defect** blocks publication. There are six small consistency fixes (§3–§5), all 0 or +1 lines.

## 1. What was checked
Tools: MSI poppler 25.11.0 fails (libstdc++ GLIBCXX mismatch), so all checks used pypdf 6.18.1 on MSI.
- **Fonts:** all Latin Modern (LMRoman 6/8/9/10, bold, italic, caps; LMMathItalic 6/8/9/10; LMMathSymbols 6/8/9/10; LMMathExtension10; LMMono9 for the DOIs) plus AMS MSAM10/MSBM10. Every font is an embedded subset, with no Type 3 fonts.
- **Link annotations per page:** [12, 14, 8, 19, 0, 11, 16, 30, 24]. Page 5 has none: the isolation step and the models cite nothing and use no \ref, which is correct.
- **Page breaks:**
  - p.1: title, abstract, Theorem 1, background; MSC and keywords at the foot;
  - p.2 opens mid-sentence ("…over a clopen tower…");
  - p.4 ends inside the proof of Corollaries 3–4;
  - p.6 ends with the SL₃(Z) paragraph, and p.7 opens "4. Word problems and factors";
  - p.7 ends with the Questions, and p.8 opens "Origin and authorship";
  - p.8–9: bibliography, [1]–[49].
  - The heuristic scan found no page ending with a section heading or a theorem/corollary opener, and no widowed heading.
- **Numbering:** Theorem 1 (thm:main), Theorem 2 (thm:general), Corollary 3 (cor:lef), Corollary 4 (cor:host), Corollary 5 (cor:wp), one shared counter. Equation (1) is eq:elementary. Every \ref and \eqref resolves; "Corollaries 3 and 4" matches.
- **Display math:** no overfull box, so no display overflows the margin.
- **Bibliography:**
  - 49 entries, en-dashes in every page range, consistent initials (`L.~O. Clark`), MathSciNet-style journal abbreviations, uniform arXiv/doi macros, "online first" for Kionke–Schesler.
  - The exceptions are §3.

## 2. Underfull box (optional, cosmetic)
The only warning is Champetier's entry: the unbreakable DOI `doi:10.1016/S0040-9383(98)00063-9` forces loose spacing (badness 1072, just above the reporting threshold). Recommendation: **no change**. The gap is not visible at normal zoom. If you want it gone, add `\usepackage{xurl}` after hyperref (+1 line), which lets `\nolinkurl` break inside DOIs; recheck the other entries afterwards.

## 3. Bibliography consistency fixes
**BIB-A (serial comma), l.753.** Every other entry with three or more authors uses the serial comma (CFKP, GPS, GPS99, KMS).
Before: `R.~Nicoara, S.~Popa and R.~Sasyk, \emph{On $\mathrm{II}_1$ factors`
After: `R.~Nicoara, S.~Popa, and R.~Sasyk, \emph{On $\mathrm{II}_1$ factors`

**BIB-B (proceedings data), l.820–823.** The other two chapters in books give publisher and city (Gromov87, Pestov–Kwiatkowska); Thompson 1980 does not.
Before:
```latex
which preserve the word problem}, in: Word problems II, Stud. Logic Found.
Math. \textbf{95} (1980), 401--441.
```
After:
```latex
which preserve the word problem}, in: Word problems II, Stud. Logic Found.
Math. \textbf{95}, North-Holland, Amsterdam (1980), 401--441.
```
(Word Problems II, eds. Adian, Boone and Higman, North-Holland 1980. The DOI prefix 10.1016/S0049-237X is the Elsevier/North-Holland series.)

**BIB-C (Rădulescu volume title), l.790.** This agrees with sk-perfect-b BIB-1: the chapter lacks its volume title.
Before: `$R^\omega$}, Theta Ser. Adv. Math. \textbf{9}, Theta, Bucharest (2008),`
After: `$R^\omega$}, in: Hot topics in operator theory, Theta Ser. Adv. Math. \textbf{9}, Theta, Bucharest (2008),`

**BIB-D (Margulis title and translation), l.731–734.** This agrees with sk-perfect-b BIB-2 (mathnet ppi925, as that lane reports; not re-read here).
Before:
```latex
G.~A. Margulis, \emph{Explicit construction of a concentrator}
(Russian), Problemy Peredachi Informatsii \textbf{9} (1973), no.~4,
71--80.
```
After (+1 line):
```latex
G.~A. Margulis, \emph{Explicit constructions of concentrators}
(Russian), Problemy Peredachi Informatsii \textbf{9} (1973), no.~4,
71--80; English transl., Problems Inform. Transmission \textbf{9} (1973),
325--332.
```

**BIB-E (order of preprint and doi), l.766–768.** Kionke–Schesler prints the journal data, then the doi, then the arXiv id; Ozawa puts the doi after the preprint clause.
Before:
```latex
Internat. J. Math. \textbf{15} (2004), 501--530; preprint \arxiv{math/0306067} (2003).
\doi{10.1142/S0129167X04002417}.
```
After:
```latex
Internat. J. Math. \textbf{15} (2004), 501--530.
\doi{10.1142/S0129167X04002417}. \arxiv{math/0306067}.
```

## 4. PDF metadata (0 lines)
**META-A, l.7.** The PDF keywords disagree with the printed keywords (l.27): "property (T)" vs "Property (T)", "LEF groups" vs "locally embeddable into finite groups", "subshifts" vs "minimal subshifts".
Before: `pdfkeywords={property (T), sofic groups, hyperlinear groups, LEF groups, simple groups, subshifts, expanders}}`
After: `pdfkeywords={Property (T), sofic groups, hyperlinear groups, locally embeddable into finite groups, simple groups, minimal subshifts, expanders}}`

## 5. MSC and keywords (optional)
- The current codes all fit the content:
  - 20E32 (simple groups), primary;
  - 05C48 (expander graphs), 16S35 (crossed products), 20E26 (residual properties), 20F10 (word problems), 22D55 (property (T)), 37B10 (symbolic dynamics), 46L10 (von Neumann algebras).
- **MSC-A (optional, 0 lines):** Corollary 5 and the word-problem clause of Corollary 3 are computability results. Add 03D40 (word problems in computability and recursion theory).
  Before: `\subjclass[2020]{Primary 20E32; Secondary 05C48, 16S35, 20E26, 20F10, 22D55, 37B10, 46L10}`
  After: `\subjclass[2020]{Primary 20E32; Secondary 03D40, 05C48, 16S35, 20E26, 20F10, 22D55, 37B10, 46L10}`
- **Keywords:** adequate. An optional addition is "word problem" (in both `\keywords` and `pdfkeywords` if adopted).

## 6. Not checked
- Visual rendering of individual glyphs (no rasterization; poppler is broken on MSI).
- Hyperlink targets (only annotation counts were checked; every link comes from `\cite`, `\ref`, `\href`, `\doi` or `\arxiv`, and 0 undefined references were logged).
- Correctness and credit: those belong to sk-perfect-a/b/c.
