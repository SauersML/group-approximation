# sk-answered-questions proposal (RULES §6): which printed questions the introduction should name

Lane sk-answered-questions, 2026-09-13. Line numbers refer to the landed rev3 on main (9047d0d3c9, md5 274f19367f7f706b05c017af721c3884). Evidence: `sk-answered-questions-2026-09-13-part2.md` §1.

## Verdict
- The note already names every printed question it answers as stated: Brown Q7, Ozawa's survey p. 527, Pestov 9.1. No lineage change.
- One new framing is worth a sentence: Corollary `cor:lef` completely answers the LEF analogue of Kionke–Schesler's printed question, and it has the shape of the Boone–Higman theorem. This merges decision 79's b-C5 (Boone–Higman parallel) and b-D3 into one paragraph (P1).
- Three conditional credit sentences (P2–P4) are needed only if the corresponding rev4 candidates enter the note.

## P1 (RECOMMEND): the opening paragraph of Section "LEF groups" (l.269–274)
(a) Current text, verbatim:
```latex
Every countable group embeds in a finitely generated simple
group~\cite{Gorjuskin,Schupp}, and Kionke and Schesler proved that every
finitely generated residually finite group embeds in a finitely generated
simple LEF group~\cite[Theorem~1.2]{KionkeSchesler}. The next corollary
adds property~\textup{(T)} and applies to every LEF group. Since LEF
passes to subgroups, it characterizes LEF groups.
```
Replacement:
```latex
Every countable group embeds in a finitely generated simple
group~\cite{Gorjuskin,Schupp}, and Kionke and Schesler proved that every
finitely generated residually finite group embeds in a finitely generated
simple LEF group~\cite[Theorem~1.2]{KionkeSchesler}. They also raised the
question which groups embed in finitely generated simple amenable groups.
For LEF groups the next corollary answers the analogous question, with a
Kazhdan host. It parallels the theorem of Boone and Higman that a finitely
generated group has solvable word problem if and only if it embeds in a
simple subgroup of a finitely presented group~\cite{BooneHigman}.
```
Bibitem, alphabetical after `BezuglyiMedynets` (Crossref-verified):
```latex
\bibitem{BooneHigman}
W.~W. Boone and G.~Higman, \emph{An algebraic characterization of groups
with soluble word problem}, J. Austral. Math. Soc. \textbf{18} (1974),
41--53. \doi{10.1017/S1446788700019108}.
```
- (b) No new proof text.
- (c) Length: +3 text lines, +4 bibliography lines.
- (d) Trade-off: the reader learns which published question the corollary settles, in its LEF form, and which classical theorem it resembles. There is no new fact to trust beyond two citations.
- Wording checks:
  - "raised the question" matches Kionke–Schesler's "it is natural to ask which groups embed into finitely generated, simple amenable groups … a complete answer … seems yet to be out of reach" (arXiv:2304.09307v1 p. 2). No page locator is given, since the journal pagination was unchecked.
  - "answers the analogous question" holds for finitely generated inputs, which is what `cor:lef` states. Do not write "answers their question": the amenable question stays open.
  - The Boone–Higman "if and only if" form is verbatim Corollary 3.7 of Belk–Bleak–Matucci–Zaremsky's progress survey, and Kourovka 20.7 prints the embedding direction with the same reference.
- If the "Since LEF passes to subgroups, it characterizes LEF groups" sentence is wanted, it can follow "with a Kazhdan host." (+1 line). P1 drops it because the corollary's own "if and only if" says it.
- (e) Status: literature facts only. `cor:lef` is reviewed.

## P2 (CONDITIONAL: only if the no-decidable-universal-host clause of item 71(d) enters the note)
The time-complexity argument has a printed precedent.
Proposed sentence after the clause:
```latex
The obstruction comes from finitely presented residually finite groups
with arbitrarily hard word problems~\cite{KMS}; compare
Rauzy~\cite[Proposition~26]{Rauzy}.
```
Bibitems (Crossref-verified):
```latex
\bibitem{KMS}
O.~Kharlampovich, A.~Myasnikov, and M.~Sapir, \emph{Algorithmically complex
residually finite groups}, Bull. Math. Sci. \textbf{7} (2017), 309--352.
\doi{10.1007/s13373-017-0103-z}.
\bibitem{Rauzy}
E.~Rauzy, \emph{Remarks and problems about algorithmic descriptions of
groups}, Internat. J. Algebra Comput. \textbf{35} (2025), 1019--1053.
\doi{10.1142/S0218196725500328}.
```
- Length: +3 text lines, +8 bibliography lines.
- Numbering: "Proposition 26" is from arXiv:2111.01190v2 p. 8; the journal numbering is unchecked. sk-wp-host cites KMS Theorem 4.21 (time complexity) and Theorem 4.19 (depth) in arXiv v5 numbering.

## P3 (CONDITIONAL: only if sk-strong-7's separable-factor paragraph passes sk-verify-10)
Printed wish, verbatim (arXiv:math/0210411v2 p. 2):
> "it would be interesting to know whether all (or at least one of) Γα 's are embeddable into the unitary group U(Rω ) of the ultrapower Rω of hyperfinite II1 -factors"

The Γ_α are Gromov's groups, so the note must not say "answers Ozawa". Safe wording:
```latex
Ozawa proved that a separable $\mathrm{II}_1$ factor contains only countably
many of Gromov's simple Kazhdan groups $\Gamma_\alpha$ in its unitary group,
and remarked that it would be interesting to know whether one of them embeds
in $U(\mathcal R^\omega)$~\cite{OzawaUniversal}. His argument applies to the
groups $G_X$, which are hyperlinear.
```
Novelty caution for sk-verify-10: a continuum of pairwise nonisomorphic property (T) group II_1 factors is already known ([CIOS21, Corollary 2.7], quoted in Chifan–Drimbe–Ioana arXiv:2205.07442 p. 2). The difference is 𝓡^ω-embeddability.

## P4 (CONDITIONAL: only if the SL_3(Z) obstruction paragraph enters the note)
- Keep sk-sl3z-bandwidth's credit to Cyr–Franks–Kra–Petite (Corollary 3.10: exponentially distorted elements do not embed into Aut(X) for zero entropy).
- Do not claim to answer their Questions 5.1–5.3. Those concern Aut(X), and Theorem D concerns GL_m(LC(X,F_q)⋊Z).
- Optional clause (+1 line, reviewed through sk-verify-8's PASS of C1): "The same bound holds in topological full groups of subshifts, which lie in $\GL_1(LC(X,\F_2)\rtimes\Z)$."
- The derived consequence that finitely generated nilpotent subgroups of [[ϕ]] are virtually abelian stays out of the note and in this artifact: unreviewed, novelty unknown.

## Rejected on reader merits
- Adding Pestov–Kwiatkowska p. 28 or the Elek–Szabó question to the lineage paragraph: the same lineage, and the lineage paragraph is the user's decision.
- Naming Cornulier's (2e) or Bradford's LEF-growth questions in the introduction: only variants.
- Any "no printed question" claim in the note: the search is bounded (part 2 §0).
