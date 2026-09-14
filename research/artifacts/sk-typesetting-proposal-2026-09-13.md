# sk-typesetting proposal: LaTeX and typographic polish of the note (2026-09-13)

Lane sk-typesetting (ROSTER-F). Target: main's `simple_kazhdan_sofic_group.tex` at e80dcf20a (revision 2, md5 4ad49212…, 386 lines). Line numbers refer to that blob. No rev3 draft existed when this was written.

Nothing here changes mathematics or wording. Every item is typography, metadata or bibliography format.

## 0. Evidence (MSI, texlive/2025, pdflatex 3 passes, `/scratch.global/sauer354/sk/sk-typesetting/`)
- **Main as landed:** 0 errors, 0 overfull, **2 underfull**, 0 undefined, 5 pages.
  - Underfull (badness 1389), bibliography lines 307–310: the Brown bibitem.
  - Underfull (badness 1132), lines 358–362: the Ozawa bibitem.
  - Cause: `\href{…}{arXiv:math/…}` sets the id as plain text with no break points.
- **Patched copy** (all items P1–P9 below applied; lane dir `patched.tex`, md5 387ee93b…, 387 lines): 0 errors, 0 overfull, **0 underfull**, 0 undefined, 5 pages.
- **Other log entries:** one benign `Package microtype Warning: Unable to apply patch 'footnote'`. The note has no footnotes, so nothing to fix. No hyperref "Token not allowed" warnings.
- **Bookmarks (main.out):**
  - "1. Proof of Theorem 1", "The ring and property (T)", "Finite models", "Simplicity", "2. Word problems", "3. Questions", "References". The `\ref` in the section title already resolves in the bookmark, so no `\texorpdfstring` is needed.
  - DEFECT: "Origin and authorship" sits as a child of "3. Questions" (P7).
- **Fonts:** T1 Latin Modern through pdfTeX, so Type 1. `pdffonts` and `pdfinfo` are not installed on MSI (command not found). A `strings` scan found no `/Type3` entries, but the object streams are compressed, so the check is bounded, not conclusive.
- **MSC2020 codes,** checked on zbMATH's classification pages today:
  - 20E32 Simple groups;
  - 05C48 Expander graphs;
  - 16S35 Twisted and skew group rings, crossed products;
  - 20E26 Residual properties and generalizations; residually finite groups;
  - 20F10 Word problems, other decision problems …;
  - 22D10 Unitary representations of locally compact groups;
  - **22D55 Kazhdan's property (T), the Haagerup property, and generalizations**;
  - 37B10 Symbolic dynamics;
  - 46L10 General theory of von Neumann algebras.

## P1. An `\arxiv` macro (removes both underfull boxes)
(a) l.17, current:
```latex
\newcommand{\doi}[1]{\href{https://doi.org/#1}{\nolinkurl{doi:#1}}}
```
Replacement (add one line):
```latex
\newcommand{\doi}[1]{\href{https://doi.org/#1}{\nolinkurl{doi:#1}}}
\newcommand{\arxiv}[1]{\href{https://arxiv.org/abs/#1}{\nolinkurl{arXiv:#1}}}
```
l.304, current `\href{https://arxiv.org/abs/2608.05362}{arXiv:2608.05362} (2026).` → `\arxiv{2608.05362} (2026).`
l.309, current `\href{https://arxiv.org/abs/math/0111286}{arXiv:math/0111286} (2001).` → `\arxiv{math/0111286} (2001).`
(c) +1 preamble line. (d) The ids can break at `/` and `:` like the DOIs, so the two loose bibliography lines disappear, and all identifiers are typeset one way.

## P2. Ozawa bibitem: DOI last, as in every other entry
(a) l.358–361, current:
```latex
N.~Ozawa, \emph{About the QWEP conjecture},
Internat. J. Math. \textbf{15} (2004), 501--530.
\doi{10.1142/S0129167X04002417}.
Preprint \href{https://arxiv.org/abs/math/0306067}{arXiv:math/0306067} (2003).
```
Replacement:
```latex
N.~Ozawa, \emph{About the QWEP conjecture},
Internat. J. Math. \textbf{15} (2004), 501--530; preprint \arxiv{math/0306067} (2003).
\doi{10.1142/S0129167X04002417}.
```
(c) −1 line. (d) The bibliography gets one uniform shape (journal data, then DOI), and the 2003 date the text relies on stays visible.

## P3. MSC2020 codes: property (T) has its own code
(a) l.25, current:
```latex
\subjclass[2020]{Primary 20E32; Secondary 05C48, 20E26, 20F10, 22D10, 37B10, 16S35}
```
Replacement:
```latex
\subjclass[2020]{Primary 20E32; Secondary 05C48, 16S35, 20E26, 20F10, 22D55, 37B10, 46L10}
```
(c) 0 lines. (d)
- MSC2020 has 22D55 for property (T), while 22D10 is unitary representations in general.
- 46L10 covers the von Neumann paragraph (l.168–177: McDuff factor, 𝓡^ω); sk-panel-referee-2 also suggested it.
- The secondary codes are in ascending order.

## P4. Keywords (amsart standard)
(a) After l.25, add:
```latex
\keywords{Property (T), sofic groups, hyperlinear groups, locally embeddable into finite groups, simple groups, minimal subshifts, expanders}
```
(c) +1 line. (d) amsart prints keywords on the first page, and journals ask for them. The list only uses terms from the abstract.

## P5. PDF metadata keywords
(a) l.7, current:
```latex
\hypersetup{pdftitle={Infinite simple Kazhdan groups that are limits of finite simple groups},pdfauthor={\paperauthorname}}
```
Replacement:
```latex
\hypersetup{pdftitle={Infinite simple Kazhdan groups that are limits of finite simple groups},pdfauthor={\paperauthorname},pdfkeywords={property (T), sofic groups, hyperlinear groups, LEF groups, simple groups, subshifts, expanders}}
```
(c) 0 lines. (d) The PDF becomes searchable by the same terms. There is no visible change.

## P6. End of the proof of Theorem 1 with amsthm's `\qed`
(a) l.237, current:
```latex
$1=1-\prod_i(1-e_{T^{a_i}V})\in J$. So $J=R$ and $N=G$.\hfill$\square$
```
Replacement:
```latex
$1=1-\prod_i(1-e_{T^{a_i}V})\in J$. So $J=R$ and $N=G$.\qed
```
(c) 0 lines. (d) It gives the same symbol as the `proof` environment of the Corollary (l.251–277), with amsthm's no-break spacing, so the square never lands alone on a line.

## P7. "Origin and authorship" is not part of §3 Questions
(a) l.293, current:
```latex
\subsection*{Origin and authorship}
```
Replacement:
```latex
\section*{Origin and authorship}
```
(c) 0 lines. (d) As printed, it is an unnumbered subsection of "3. Questions", and the PDF bookmark nests it under Questions. The replacement makes it a separate end-matter heading. Checked in patched.out, where it now appears at the top level.

## P8. Kirchberg title: WITHDRAWN (no change)
(a) l.341, current `E.~Kirchberg, \emph{Discrete groups with Kazhdan's property~$T$ and` → `E.~Kirchberg, \emph{Discrete groups with Kazhdan's property~T and`
Crossref (10.1007/BF01459798) gives the title string "Discrete groups with Kazhdan's propertyT and factorization property are residually finite". The run-together "propertyT" indicates the T was formatted separately (italic) in print, so the current `property~$T$` is closer to the printed title than an upright T. Keep l.341 as it is. The patched copy in the lane dir includes the withdrawn P8; drop that one line when applying.

## P9. Stepanov: the AMS journal abbreviation
(a) l.370, current `group over a ring}, Zap. Nauchn. Sem. POMI \textbf{236} (1997), 166--182;` → `group over a ring}, Zap. Nauchn. Sem. S.-Peterburg. Otdel. Mat. Inst. Steklov. (POMI) \textbf{236} (1997), 166--182;`
(c) 0 lines, but the source line is longer. The patched compile has no overfull box. (d) It matches the MathSciNet abbreviation, as the other entries already use AMS abbreviations (Invent. Math., Internat. J. Math., J. Reine Angew. Math.).

## Checked, no change recommended
- Every `\cite` is preceded by `~` (19 citations grepped; none without it).
- "property~\textup{(T)}" is used consistently in running text. The subsection heading "The ring and property (T)" is a bold run-in heading, already upright.
- No `\texorpdfstring` needed for `\section{Proof of Theorem~\ref{thm:main}}`: the bookmark reads "1. Proof of Theorem 1".
- The bibliography is in alphabetical order; author initials use `~`; there are three authors with the serial comma (GPS).
- Macros `\PSL`, `\SL`, `\doi` are all used; nothing defined is unused.
- `\epsilon_{ab}` versus `\varepsilon_{ab}`: a neutral choice, so no change.
- The benign microtype footnote warning (see §0).

## Status
- Typography only. No Cairn nodes, no review requested (no mathematical claim).
- The patched copy `sk/lanes/sk-typesetting/patched.tex` (md5 387ee93b…) compiles clean with P1–P9 applied. P8 is withdrawn (keep `property~$T$`), which does not affect the compile. Main can apply P1–P7 and P9 in one edit.
- Crossref also confirms the Stepanov title and journal (J. Math. Sci.) for DOI 10.1007/BF02169976.
