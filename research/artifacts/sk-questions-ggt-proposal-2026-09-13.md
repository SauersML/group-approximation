# sk-questions-ggt proposal (RULES §6): group-theory and dynamics questions, and what the note should say

Evidence: `sk-questions-ggt-literature-2026-09-13-part1.md` (cd2f758f80) and part 2 (same landing as this file).
Line numbers are those of `$SK/manuscript-disk-1646.tex`. It is identical to main's `simple_kazhdan_sofic_group.tex` at bf961c128 (md5 7b3dc4ec…).

## Verdict
Within the bound of parts 1–2, the group-theory and dynamics literature prints ONE question that G_X answers as stated: Ozawa's question, as restated by Pestov and again by Pestov–Kwiatkowska (arXiv:0911.4266, p. 28, "it remains in particular unknown whether finitely generated simple Kazhdan groups can be hyperlinear/sofic").
- That lineage is already in the note and is the user's decision.
- No other printed question in these areas is answered as stated. So this lane proposes NO new corollary sentence.
- Below are one citation precision fix (P1), one optional closing question (P2), and two conditional credit sentences for other lanes (P3, P4).

## P1. Thom citation: the theorem number points to a different statement (l.63–65)
(a) Current text, verbatim:
```
Thom had already constructed a finitely generated Kazhdan LEF group
that is not residually finite~\cite[Theorem~1.4]{Thom}; his example
is not simple.
```
Replacement:
```
Thom had already constructed a finitely generated Kazhdan LEF group
that is not residually finite~\cite{Thom}; his example
is not simple.
```
(b) No proof text.
(c) Length change: 0 lines.
(d) Reader trade-off: the pointer no longer sends the reader to a theorem that states something else.
- Thom's Theorem 1.4 (arXiv:0810.2180 v1) reads: "There exists a finitely generated Kazhdan group G which is locally embeddable into finite groups (in particular sofic and hence hyperlinear) but does not have the factorization property."
- Non-residual finiteness is stated in the abstract ("an example of a sofic Kazhdan group which is not residually finite") and on p. 3.
- The journal numbering (Groups Geom. Dyn. 4 (2010)) was not checked, which is a second reason to drop the number.
(e) Status: a literature fact, checked against the arXiv PDF. It is for sk-citations to merge with any overlapping fix.

## P2. Optional: a closing question with its printed sources (inserted after l.262)
(a) Current text: the note goes from `\end{proof}` (l.262) straight to `\subsection*{Origin and authorship}` (l.264). Proposed insertion after l.262:
```
\subsection*{A question}
Finitely presented LEF groups are residually finite~\cite{VershikGordon},
so the groups $G_X$ are not finitely presented. Caprace and R\'emy
constructed infinite finitely presented simple Kazhdan groups~\cite{CapraceRemy}.
Is there an infinite finitely presented simple Kazhdan group that is sofic?
A positive answer would give a finitely presented sofic Kazhdan group that is
not residually finite, as asked by Alekseev and Thom~\cite[Open problem~6.1]{AlekseevThom}.
```
New bibitems:
```
\bibitem{AlekseevThom}
V.~Alekseev and A.~Thom, \emph{Centralizers of sofic approximations of Kazhdan groups},
\href{https://arxiv.org/abs/2608.05362}{arXiv:2608.05362} (2026).

\bibitem{CapraceRemy}
P.-E.~Caprace and B.~R\'emy, \emph{Simplicity and superrigidity of twin building lattices},
Invent. Math. \textbf{176} (2009), 169--221.
\doi{10.1007/s00222-008-0162-6}.

\bibitem{VershikGordon}
A.~M. Vershik and E.~I. Gordon, \emph{Groups that are locally embeddable in the class
of finite groups}, Algebra i Analiz \textbf{9} (1997), no.~1, 71--97; English transl.,
St. Petersburg Math. J. \textbf{9} (1998), no.~1, 49--67.
```
(b) Proof of the only claim: G_X is LEF, infinite and simple. A finitely presented LEF group is residually finite, and an infinite simple group is not. So G_X is not finitely presented.

(c) Length change: +8 lines of body and +12 lines of bibliography.

(d) Reader trade-off.
- Gains: a true one-sentence fact about G_X (not finitely presented), and the sharp next question with its printed neighbors.
- The reader must trust Vershik–Gordon's theorem, which is standard.
- Cost: about 20 lines in a note whose order is "short". My own verdict: the first sentence alone earns its place, while the question and its two citations are a style call for the user.

(e) Sources and status:
- The Vershik–Gordon attribution is taken from Kionke–Schesler (arXiv:2304.09307, l.1674–1676: "A finitely presented LEF group is residually finite; see [72]", where [72] is Vershik–Gordon). I did not open Vershik–Gordon's paper. Its bibliographic data come from the repo's earlier source notes and are not in Crossref.
- Caprace–Rémy, verbatim (arXiv:math/0607664 v2, p. 2): "As pointed out to us by Y. Shalom, we obtain the first infinite finitely presented discrete groups to be both simple and Kazhdan."
- Alekseev–Thom Open problem 6.1, verbatim: "Are there examples of finitely presented sofic groups with Kazhdan's property (T) that are not residually finite?"
- The Cairn claim for the question is `sofic-fp-simple-kazhdan-group-from-fp-simple-ring` (sk-fp-sofic-a, OPEN), with root `hyperlinear-fp-infinite-simple-group`.
- Deliberately omitted: any sentence saying the soficity of the Kac–Moody lattices is unknown. I found no printed source for that status (Cornulier's printed "not known if they are sofic" is about different, non-simple isolated Kazhdan groups), so it would be an unverified negative claim.

## P3. Conditional credit sentence, needed only if sk-universal-embedding-a lands a (T) embedding corollary
The prior result without property (T): Kionke–Schesler, arXiv:2304.09307 v1, Theorem 1.2 (= Theorem 9.14):
- abstract: "every finitely generated residually finite (amenable) group embeds into a finitely generated (amenable) LEF simple group";
- journal version: J. Comb. Algebra (2024), doi:10.4171/jca/103. The Crossref record has no volume or pages.

Template, for use only once such a corollary exists:
```
Without property~\textup{(T)}, Kionke and Schesler embedded every finitely generated
residually finite group in a finitely generated simple LEF group~\cite{KionkeSchesler}.
```
- +2 lines and one bibitem.
- Leave the theorem number out until the journal numbering is checked.

## P4. Conditional credit sentence, needed only if sk-lef-growth lands the S_X LEF-growth theorem
The main node `elementary-group-lef-growth-separates-subshifts` is OPEN, with the lower bound as the crux. If it lands, the note must credit:
- Bradford (J. Algebra 608 (2022) 214–238, doi:10.1016/j.jalgebra.2022.04.039), who introduced LEF growth and asked "What is the LEF growth of [[T]]′? How does it depend on the dynamical properties of (X, T)?" (arXiv:2104.07111, Question 7.2; journal numbering unchecked);
- Bradford–Dona (Ergodic Theory Dynam. Systems 43 (2023) 1492–1510, doi:10.1017/etds.2022.12), Theorem 1.1: ℒ_Γ(n) ⪯ (2R_X(n))! for f.g. Γ ≤ ⟦σ⟧, plus a continuum of LEF groups separated by LEF growth.

A G_X version is a Kazhdan-simple instance of these results, not an answer to a printed question.

## Rejected on reader merits
- **A sentence on Thom's "intriguing question".** Thom (arXiv:0810.2180, p. 3) asks whether Champetier's Kazhdan groups without finite-index subgroups can be hyperlinear. G_X is a hyperlinear, even LEF, Kazhdan group with no proper finite-index subgroup, but it is not one of Champetier's groups. A sentence would invite the misreading that the note answers Thom's question, and the reader gains little.
- **Cornulier's Bourbaki questions (2f), (3) and (8)** are about [[ϕ]]′. Their G_X analogues (classification; number of generators) belong to sk-rigidity-* and sk-generators, and only a theorem from those lanes would justify a sentence.
